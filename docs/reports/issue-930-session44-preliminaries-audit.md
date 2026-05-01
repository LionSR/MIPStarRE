# Issue #930 session 44 preliminaries discrepancy audit

Audit date: 2026-05-01

Base commit: `51b74c68` (`origin/main` when this worktree was created)

Branch: `gpt55/session44-930-discrepancy-audit-next`

## Executive summary

I audited a new non-overlapping slice of already-formalized LDT statements in the preliminaries chapter:

- finite-field trace and Fourier orthogonality in `MIPStarRE/LDT/Preliminaries/FiniteFields.lean`, against `references/ldt-paper/preliminaries.tex:15-83` and `blueprint/src/chapter/ch03_preliminaries.tex:13-72`;
- low-individual-degree polynomial definitions and Schwartz--Zippel wrappers in `MIPStarRE/LDT/Preliminaries/Polynomials.lean`, `MIPStarRE/LDT/Basic/LowDegreePolynomial.lean`, and `MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean`, against `references/ldt-paper/preliminaries.tex:87-123` and `blueprint/src/chapter/ch03_preliminaries.tex:74-131`;
- the project-level pointwise polynomial agreement package `polynomialAgreement_avg_le_mdq`, against its intended use in `references/ldt-paper/inductive_step.tex:119-133` and `blueprint/src/chapter/ch03_preliminaries.tex:118-131`.

This scope avoids the active areas for #1000 (`MIPStarRE/LDT/Tactic/AvgCongr.lean`), #998 (`MIPStarRE/LDT/Commutativity/Transport/FullSlice*`), #997 (`MIPStarRE/LDT/Basic/DistributionPMF.lean` and `DistributionMeasure.lean`), and the draft #889 Lean/Mathlib upgrade.  It also avoids the session 42 #930 slice: expansion/hypercube graph and global variance were not re-audited here.

Verdict: I found no undocumented mathematical discrepancy in this slice, and I did not create a new `docs/paper-gaps/` note.  The formal statements preserve the paper's finite-field trace convention, Fourier orthogonality facts, polynomial-representative convention, and the `md/q` Schwartz--Zippel loss used in the induction step.  The only non-paper-literal aspect is an implementation choice: Lean defines the trace using Mathlib's algebraic trace and proves the Frobenius-sum formula in adjacent theorems.  This is mathematically equivalent to the paper's definition and is not a paper gap.

## Validation

Targeted Lean checks in this worktree succeeded:

```text
lake env lean MIPStarRE/LDT/Preliminaries/FiniteFields.lean
lake env lean MIPStarRE/LDT/Preliminaries/Polynomials.lean
lake env lean MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean
lake env lean MIPStarRE/LDT/Basic/LowDegreePolynomial.lean
lake env lean MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean
```

A scratch `#check`/`#print axioms` file was also run for the audited public declarations.  For `fourier_fact_scalar`, `fourier_fact_vector`, `schwartzZippel_individualDegree`, and `polynomialAgreement_avg_le_mdq`, `#print axioms` reported only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; no audited theorem reported `sorryAx`.

A grep over the audited files found no `sorry`, `axiom`, or `admit` in the checked slice.

## Finding 1: finite-field trace and Fourier orthogonality match the paper

The paper fixes a prime power `q = p^t`, writes `ω = e^{2πi/p}`, and defines the finite-field trace by the Frobenius sum

```text
tr[x] = sum_{ℓ=0}^{t-1} x^(p^ℓ)
```

in `references/ldt-paper/preliminaries.tex:15-27`.  The blueprint states the same definition in `def:ff-trace` (`blueprint/src/chapter/ch03_preliminaries.tex:13-22`).

Lean implements `ffTrace` as Mathlib's algebraic trace `Algebra.trace (ZMod p) F` (`MIPStarRE/LDT/Preliminaries/FiniteFields.lean:35-40`).  The Frobenius-sum formula is not omitted: `algebraMap_ffTrace_eq_sum_pow` proves the general finite-field formula after applying the prime-field inclusion (`MIPStarRE/LDT/Preliminaries/FiniteFields.lean:42-50`), and `honestFq_algebraMap_ffTrace_eq_sum_pow` specializes it to the project's honest field model with exactly `spec.n` Frobenius powers (`MIPStarRE/LDT/Preliminaries/FiniteFields.lean:58-69`).  This is an implementation of the paper's trace, not a change of mathematical content.

The two Fourier facts also match.  The paper states the scalar and vector orthogonality identities in `references/ldt-paper/preliminaries.tex:29-83`; the blueprint repeats them as `prop:fourier-fact-scalar` and `prop:fourier-fact-vector` (`blueprint/src/chapter/ch03_preliminaries.tex:24-72`).  Lean's `fourier_fact_scalar` proves

```lean
𝔼 x : F, ffChar (x * a) = if a = 0 then 1 else 0
```

for finite fields over `ZMod p` (`MIPStarRE/LDT/Preliminaries/FiniteFields.lean:123-143`), and `fourier_fact_vector` proves the same statement for the additive character of the dot product on `Fin m -> F` (`MIPStarRE/LDT/Preliminaries/FiniteFields.lean:206-223`).  The formal proof uses Mathlib additive-character orthogonality instead of the paper's translation-invariance calculation, but the hypotheses and conclusions are the same.

## Finding 2: low-degree polynomial objects use representatives, as the blueprint says

The paper defines `\polyfunc{m}{q}{d}` as polynomials over `F_q^m` with individual degree at most `d` (`references/ldt-paper/preliminaries.tex:87-102`).  The blueprint makes the finite-field subtlety explicit: elements are polynomial representatives, not functions modulo pointwise equality (`blueprint/src/chapter/ch03_preliminaries.tex:74-88`).

Lean follows this convention.  `polyFunc m K d` is `MvPolynomial.restrictDegree (Fin m) K d` (`MIPStarRE/LDT/Preliminaries/Polynomials.lean:25-29`), while the project-level `Polynomial params` structure stores an actual multivariate polynomial and a proof that each variable has degree at most `params.d` (`MIPStarRE/LDT/Basic/LowDegreePolynomial.lean:12-15`).  The finite-answer instance transports `Polynomial params` to Mathlib's restricted-degree submodule, so the project object is finite for the same representative-based reason (`MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean:94-120`).

This matters because distinct low-degree representatives over a finite field can induce the same function when degrees are large enough.  The audited Lean statements preserve the representative-based distinctness used by the blueprint: `polynomialAgreement_avg_le_mdq` assumes `g ≠ g'` as polynomial outcomes and converts this to inequality of the stored polynomials before applying Schwartz--Zippel (`MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean:105-128`).  I found no hidden replacement by extensional equality of functions.

## Finding 3: the Schwartz--Zippel constants are unchanged

The paper's total-degree Schwartz--Zippel lemma gives an agreement probability at most `d/q`, and its individual-degree corollary gives `md/q` (`references/ldt-paper/preliminaries.tex:107-123`).  The blueprint states the same constants in `lem:schwartz-zippel-total-degree` and `lem:schwartz-zippel-individual` (`blueprint/src/chapter/ch03_preliminaries.tex:90-116`).

Lean's `schwartzZippel_totalDegree` is slightly more explicit about the degree bound: it assumes `g.totalDegree ≤ d` and `h.totalDegree ≤ d`, then proves the agreement probability is at most `d / |K|` (`MIPStarRE/LDT/Preliminaries/Polynomials.lean:86-106`).  This is the standard “degree at most `d`” reading of the paper's phrase “total degree `d`,” and it is not a strengthening of the conclusion.  Lean's `schwartzZippel_individualDegree` then derives `m*d / |K|` for two distinct elements of `polyFunc m K d` (`MIPStarRE/LDT/Preliminaries/Polynomials.lean:108-123`).  This matches the blueprint and the paper's corollary.

## Finding 4: the packaged `md/q` point-agreement bound matches the induction step

The paper's induction step uses Schwartz--Zippel to replace the averaged collision term

```text
E_u sum_{g != h} 1[g(u)=h(u)] <ψ|G^A_g ⊗ G^B_h|ψ>
```

by an `md/q` loss (`references/ldt-paper/inductive_step.tex:119-128`), yielding the displayed `ζ_1 = 2σ + 2√(3ε + 2σ) + md/q` in `references/ldt-paper/inductive_step.tex:130-133`.  The blueprint packages the scalar part of this estimate as `lem:polynomial-agreement-mdq` (`blueprint/src/chapter/ch03_preliminaries.tex:118-131`).

Lean's `polynomialAgreement_avg_eq_scalarDomain` first reindexes coded `Point params` values to the scalar domain `Fin params.m -> Scalar params` (`MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean:33-93`).  `polynomialAgreement_avg_le_mdq` then proves

```lean
avgOver (uniformDistribution (Point params))
  (fun u => if g u = g' u then 1 else 0) ≤
(params.m * params.d) / params.q
```

for distinct polynomial outcomes `g` and `g'` (`MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean:95-175`).  The formal `FieldModel params.q` assumption is just the formal ambient finite field `F_q`; it is not an additional mathematical hypothesis beyond the paper's setting.  The scalar loss and quantification match the paper use.

## Boundary of this audit

I did not re-audit `lem:generalize-b`, the hypercube graph, local/global variance, or the global-variance-of-points route, because those were the session 42 #930 slice.  I also did not audit the active distribution adapters, full-slice commutativity transport, or the `avg_congr` tactic prototype.  The present negative finding is therefore limited to the preliminaries finite-field/Fourier/Schwartz--Zippel package and its project-level `md/q` point-agreement wrapper.
