import MIPStarRE.LDT.Pasting.Bernoulli.Recurrence
import MIPStarRE.LDT.Pasting.BridgeLemmas.Final

/-!
# Section 12 pasting: final pasting theorems

Final completeness and pasting wrappers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def ldPastingTheta (params : Parameters) : Error :=
  1 / (200 * (params.m : Error))

private lemma ldPastingTheta_pos (params : Parameters) :
    0 < ldPastingTheta params := by
  unfold ldPastingTheta
  have hm : (0 : Error) < (params.m : Error) := by
    exact_mod_cast params.hm
  have hden : (0 : Error) < 200 * (params.m : Error) := by
    nlinarith
  simpa [one_div] using inv_pos.mpr hden

private lemma ldPastingTheta_lt_one (params : Parameters) :
    ldPastingTheta params < 1 := by
  unfold ldPastingTheta
  have hden : (1 : Error) < 200 * (params.m : Error) := by
    have hm : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast (Nat.succ_le_of_lt params.hm)
    nlinarith
  simpa [one_div] using inv_lt_one_of_one_lt₀ hden

private lemma subMeasMass_le_one
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    {Outcome : Type*} [Fintype Outcome] (A : SubMeas Outcome ι) :
    subMeasMass ψ A ≤ 1 := by
  unfold subMeasMass
  calc
    ev ψ A.total ≤ ev ψ (1 : MIPStarRE.Quantum.Op ι) :=
      ev_mono ψ _ _ A.total_le_one
    _ = 1 := ev_one_of_isNormalized ψ hψ

private lemma complete_nonneg_kappa
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (kappa : Error)
    (hcomplete : family.Complete strategy.state kappa) :
    0 ≤ kappa := by
  have hmass_le : subMeasMass strategy.state family.averagedSubMeas.liftLeft ≤ 1 :=
    subMeasMass_le_one strategy.state strategy.isNormalized family.averagedSubMeas.liftLeft
  have hmass_ge : 1 - kappa ≤ subMeasMass strategy.state family.averagedSubMeas.liftLeft := by
    simpa [subMeasMass] using hcomplete.averageCompleteness.lowerBound
  linarith

private lemma ldPastingTheta_kappa_fraction_le
    (params : Parameters) (kappa : Error)
    (hkappa : 0 ≤ kappa) :
    kappa / (1 - ldPastingTheta params) ≤
      kappa * (1 + 1 / (100 * (params.m : Error))) := by
  have hm : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hden : (1 : Error) < 200 * (params.m : Error) := by
    nlinarith
  have hx0 : (0 : Error) < 200 * (params.m : Error) := by positivity
  have hx1 : (0 : Error) < 200 * (params.m : Error) - 1 := by
    nlinarith
  have hxne : (200 * (params.m : Error)) ≠ 0 := by positivity
  have hx1ne : (200 * (params.m : Error) - 1) ≠ 0 := by linarith
  have hfrac : (1 : Error) / (1 - ldPastingTheta params) ≤ 1 + 1 / (100 * (params.m : Error)) := by
    unfold ldPastingTheta
    field_simp [hxne, hx1ne]
    nlinarith
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hfrac hkappa

private lemma ldPastingTheta_exp_exponent
    (params : Parameters) (k : ℕ) :
    -((ldPastingTheta params ^ (2 : ℕ)) * (k : Error)) / 2 =
      -((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))) := by
  unfold ldPastingTheta
  have hmne : (params.m : Error) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt params.hm
  have hden : (200 * (params.m : Error)) ≠ 0 := by positivity
  field_simp [hden, hmne]
  ring

private lemma ldPastingTheta_chernoff_lowerBound
    (params : Parameters) (kappa nu : Error) (k : ℕ)
    (hkappa : 0 ≤ kappa) :
    1 - kappa / (1 - ldPastingTheta params) -
        Real.exp (-((ldPastingTheta params ^ (2 : ℕ)) * (k : Error)) / 2) - nu
      ≥ ldPastingCompletenessLowerBound params kappa nu k := by
  rw [ldPastingCompletenessLowerBound, ldPastingTheta_exp_exponent]
  have hfrac := ldPastingTheta_kappa_fraction_le params kappa hkappa
  linarith

private lemma idxSubMeasMass_unit
    (ψ : QuantumState ι) (A : IdxSubMeas Unit Unit ι) :
    idxSubMeasMass ψ (uniformDistribution Unit) A = subMeasMass ψ (A ()) := by
  simp [idxSubMeasMass, avgOver, uniformDistribution, subMeasMass]

private lemma sddError_unit
    (ψ : QuantumState ι) (A B : IdxSubMeas Unit Unit ι) :
    sddError ψ (uniformDistribution Unit) A B = qSDD ψ (A ()) (B ()) := by
  simp [sddError, avgOver, uniformDistribution]

private lemma bipartiteConsError_unit
    (ψ : QuantumState (ι × ι))
    (A B : IdxSubMeas Unit Unit ι) :
    bipartiteConsError ψ (uniformDistribution Unit) A B =
      qBipartiteConsDefect ψ (A ()) (B ()) := by
  simp [bipartiteConsError, avgOver, uniformDistribution]

private lemma unit_subMeas_mass_gap_le_sqrt_qSDD
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Unit ι) :
    |subMeasMass ψ A - subMeasMass ψ B| ≤ Real.sqrt (qSDD ψ A B) := by
  have hA : A.outcome () = A.total := by simpa using A.sum_eq_total
  have hB : B.outcome () = B.total := by simpa using B.sum_eq_total
  have hAherm : A.totalᴴ = A.total :=
    (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hBherm : B.totalᴴ = B.total :=
    (Matrix.nonneg_iff_posSemidef.mp B.total_nonneg).isHermitian.eq
  have hcs := ev_abs_mul_le_sqrt ψ (A.total - B.total) (1 : MIPStarRE.Quantum.Op ι)
  have hone : Real.sqrt (ev ψ ((1 : MIPStarRE.Quantum.Op ι)ᴴ * (1 : MIPStarRE.Quantum.Op ι))) = 1 := by
    rw [show ((1 : MIPStarRE.Quantum.Op ι)ᴴ * (1 : MIPStarRE.Quantum.Op ι)) = (1 : MIPStarRE.Quantum.Op ι) by simp]
    rw [ev_one_of_isNormalized ψ hψ]
    norm_num
  have hleft :
      |ev ψ ((A.total - B.total) * (1 : MIPStarRE.Quantum.Op ι))| ≤ Real.sqrt (qSDD ψ A B) := by
    calc
      |ev ψ ((A.total - B.total) * (1 : MIPStarRE.Quantum.Op ι))|
        ≤ Real.sqrt (ev ψ ((A.total - B.total) * (A.total - B.total)ᴴ)) *
            Real.sqrt (ev ψ ((1 : MIPStarRE.Quantum.Op ι)ᴴ * (1 : MIPStarRE.Quantum.Op ι))) := hcs
      _ = Real.sqrt (ev ψ ((A.total - B.total)ᴴ * (A.total - B.total))) * 1 := by
            rw [hone]
            congr 1
            have hdiff_herm : (A.total - B.total)ᴴ = A.total - B.total := by
              simp [hAherm, hBherm]
            rw [hdiff_herm]
      _ = Real.sqrt (qSDD ψ A B) := by
            simp [qSDD, qSDDCore, hA, hB]
  have hmass :
      subMeasMass ψ A - subMeasMass ψ B = ev ψ ((A.total - B.total) * (1 : MIPStarRE.Quantum.Op ι)) := by
    rw [subMeasMass, subMeasMass, ← ev_sub]
    simp
  calc
    |subMeasMass ψ A - subMeasMass ψ B|
      = |ev ψ ((A.total - B.total) * (1 : MIPStarRE.Quantum.Op ι))| := by rw [hmass]
    _ ≤ Real.sqrt (qSDD ψ A B) := hleft

private lemma unit_sddRel_mass_transfer
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : IdxSubMeas Unit Unit ι) (ε : Error)
    (hAB : SDDRel ψ (uniformDistribution Unit) A B ε) :
    subMeasMass ψ (A ()) ≥ subMeasMass ψ (B ()) - Real.sqrt ε := by
  rcases hAB with ⟨hε⟩
  have hsdd : qSDD ψ (A ()) (B ()) ≤ ε := by
    simpa [sddError_unit] using hε
  have hgap : |subMeasMass ψ (A ()) - subMeasMass ψ (B ())| ≤ Real.sqrt ε := by
    calc
      |subMeasMass ψ (A ()) - subMeasMass ψ (B ())| ≤ Real.sqrt (qSDD ψ (A ()) (B ())) :=
        unit_subMeas_mass_gap_le_sqrt_qSDD ψ hψ (A ()) (B ())
      _ ≤ Real.sqrt ε := Real.sqrt_le_sqrt hsdd
  linarith [abs_le.mp hgap]

private lemma unit_sddRel_completeness_transfer
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : IdxSubMeas Unit Unit ι) (ε r : Error)
    (hAB : SDDRel ψ (uniformDistribution Unit) A B ε)
    (hB : CompletenessAtLeast ψ (B ()) r) :
    CompletenessAtLeast ψ (A ()) (r - Real.sqrt ε) := by
  constructor
  have hmass := unit_sddRel_mass_transfer ψ hψ A B ε hAB
  linarith [hmass, hB.lowerBound]

private lemma unit_sddRel_completeness_transfer_triangle
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B C : IdxSubMeas Unit Unit ι) (ε₁ ε₂ r : Error)
    (hAB : SDDRel ψ (uniformDistribution Unit) A B ε₁)
    (hBC : SDDRel ψ (uniformDistribution Unit) B C ε₂)
    (hC : CompletenessAtLeast ψ (C ()) r) :
    CompletenessAtLeast ψ (A ()) (r - Real.sqrt (2 * (ε₁ + ε₂))) := by
  have hAC : SDDRel ψ (uniformDistribution Unit) A C (2 * (ε₁ + ε₂)) :=
    Preliminaries.stateDependentDistanceRel_triangle ψ (uniformDistribution Unit) A B C ε₁ ε₂ hAB hBC
  exact unit_sddRel_completeness_transfer ψ hψ A C (2 * (ε₁ + ε₂)) r hAC hC

private lemma ldPastingNCompleteness_of_chain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (kappa nu₇ nu₈ : Error) (k : ℕ)
    (hcomplete : family.Complete strategy.state kappa)
    (hOAO : SDDRel strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constructedPastedMeasurementTotal params family k))
      (IdxSubMeas.liftLeft (allOutcomesExpansionFamily params strategy family k))
      nu₇)
    (hHTG : SDDRel strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (allOutcomesExpansionFamily params strategy family k))
      (IdxSubMeas.liftLeft (bernoulliTailFromFamily params family k))
      nu₈)
    (hchernoff : CompletenessAtLeast strategy.state (IdxSubMeas.liftLeft (bernoulliTailFromFamily params family k) ())
      (1 - kappa / (1 - ldPastingTheta params) -
        Real.exp (-((ldPastingTheta params ^ (2 : ℕ)) * (k : Error)) / 2))) :
    CompletenessAtLeast strategy.state (IdxSubMeas.liftLeft (constructedPastedMeasurementTotal params family k) ())
      (1 - kappa / (1 - ldPastingTheta params) -
        Real.exp (-((ldPastingTheta params ^ (2 : ℕ)) * (k : Error)) / 2) -
        Real.sqrt (2 * (nu₇ + nu₈))) := by
  have hchain := unit_sddRel_completeness_transfer_triangle strategy.state strategy.isNormalized
    (IdxSubMeas.liftLeft (constructedPastedMeasurementTotal params family k))
    (IdxSubMeas.liftLeft (allOutcomesExpansionFamily params strategy family k))
    (IdxSubMeas.liftLeft (bernoulliTailFromFamily params family k))
    nu₇ nu₈
    (1 - kappa / (1 - ldPastingTheta params) -
      Real.exp (-((ldPastingTheta params ^ (2 : ℕ)) * (k : Error)) / 2))
    hOAO hHTG hchernoff
  simpa using hchain

private lemma constructedPastedMeasurementTotal_apply
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    constructedPastedMeasurementTotal params family k () =
      postprocess (constructedPastedSubMeas params family k) (fun _ => ()) := by
  rfl

private lemma bernoulliTailFromFamily_apply
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    bernoulliTailFromFamily params family k () =
      let Y := bernoulliTailOperator k params.d ((IdxPolyFamily.averagedSubMeas family).total)
      ({ outcome := fun _ => Y
         total := Y
         outcome_pos := by
           intro _
           let G := (IdxPolyFamily.averagedSubMeas family).total
           have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
           have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
           simpa [G] using bernoulliTailOperator_nonneg k params.d G hG hGle
         sum_eq_total := by simp
         total_le_one := by
           let G := (IdxPolyFamily.averagedSubMeas family).total
           have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
           have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
           simpa [Y, G] using bernoulliTailOperator_le_one k params.d G hG hGle } : SubMeas Unit ι) := by
  rfl

/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  -- Chain the three completeness-chain lemmas (§9.4 of the paper)
  have _hOAO := overAllOutcomes params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le
    family hcons hself hbound k
  constructor -- LdPastingNCompletenessStatement
  · exact hk -- largeEnough: 400 * m * d ≤ k
  · -- completenessBound
    constructor -- CompletenessAtLeast
    /- Paper: `cor:ld-pasting-N-completeness` (ld-pasting.tex lines 1798–1849).
    Chains: overAllOutcomes (ν₇) + fromHToG (ν₈) → SDDRel H vs F(G);
    chernoffBernoulliMatrix (θ = 1/(200m)): ev ψ F(G) ≥ 1-κ/(1-θ)-exp(...);
    SDDRel → mass transfer: ev ψ H ≥ ev ψ F(G) - √(ν₇+ν₈);
    parameter match: κ/(1-θ) ≤ κ(1+1/(100m)),
    exp(-θ²k/2) = exp(-k/(80000m²)).
    Requires: SDDRel → completeness transfer for Unit-indexed families. -/
    sorry

/-- `lem:ld-pasting-sub-measurement`. -/
lemma ldPastingSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedSubMeas params family k, ?_⟩
  have hconsistency :=
    hAConsistency_submeas params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  exact
    { largeEnough := hk
      constructedSubMeas := rfl
      pointConsistency := hconsistency
      completeness := hcompleteness.completenessBound }

/-- `thm:ld-pasting`. -/
theorem ldPasting
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedMeasurement params family k, ?_⟩
  have hsubmeasConsistency :=
    hAConsistency_submeas params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  have hconsistency :=
    hAConsistency_completed params strategy eps delta gamma kappa zeta
      strategy.isNormalized family k hsubmeasConsistency hcompleteness.completenessBound
  exact
    { largeEnough := hk
      constructedMeasurement := rfl
      pointConsistency := hconsistency }

end MIPStarRE.LDT.Pasting
