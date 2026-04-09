# Deep Audit: Pasting and Self-Improvement Chapters

Scope:
- Style guide: `docs/blueprint_style_guide.md`
- Paper sources:
  - `references/ldt-paper/ld-pasting.tex`
  - `references/ldt-paper/self_improvement.tex`
- Blueprint chapters:
  - `blueprint/src/chapter/ch09_pasting.tex`
  - `blueprint/src/chapter/ch07_self_improvement.tex`

Method notes:
- I did a line-by-line read of both blueprint chapters and the corresponding paper source.
- For copy-paste ratio, I used exact normalized line overlap only as a lower bound, then adjusted upward by manual spot-checking of near-verbatim prose and displayed derivations.
- For labels, I compared all `\label{...}` occurrences directly.
- For equation-label placement, I compared whether each shared `eq:` label sits inside or outside a `proof` environment in paper vs. blueprint.
- For `\uses{}`, I checked whether the dependency belongs to the statement or the proof under the style guide's "statement uses vs proof uses" rule.

## Chapter 09: `ch09_pasting`

### 1. Copy-paste ratio

Rough estimate:
- Verbatim or near-verbatim from paper: about 35% to 45%
- Genuinely rewritten / compressed: about 55% to 65%

Lower bound from exact normalized line overlap:
- 94 / 875 nonempty blueprint lines = 10.7%

Why the real copy fraction is higher than 10.7%:
- A lot of displayed equations are copied with only notation normalization (`\ot` vs `\otimes`, spacing, `\Cref` vs `\ref`).
- Several long proof passages preserve the paper's derivation order and sentence structure while lightly rewriting connective prose.
- The two largest risks are `lem:commutativity-switcheroo` and especially `lem:from-H-to-G`.

Concrete near-copy passages:

1. `cor:commuting-with-G-complete`

Blueprint:
> "Applying Lemma~\ref{lem:commutativity-switcheroo} to \ref{eq:com-main-copy}, with `\{M_o^y\}` equal to the outcome family `\{G_h^y\}`, gives"

Paper:
> "Now we apply \Cref{lem:commutativity-switcheroo} to \Cref{eq:com-main-copy}."

And immediately after:

Blueprint:
> "Applying Lemma~\ref{lem:commutativity-switcheroo} again to \ref{eq:applied-the-lemma-to-com-main-copy}, now with the one-outcome family `M_o^y = G^y`, gives"

Paper:
> "Next, we apply \Cref{lem:commutativity-switcheroo} to \Cref{eq:applied-the-lemma-to-com-main-copy}."

Assessment: lightly rewritten, but still clearly paper-derived.

2. `lem:commutativity-switcheroo`

Blueprint:
> "The fourth term in \ref{eq:g-commute-with-gg-error} is the Hermitian conjugate of the third term, so it satisfies the same bound. Summing the four errors gives"

Paper:
> "The fourth term in \Cref{eq:g-commute-with-gg-error} is the Hermitian conjugate of the third term. As a result, \Cref{eq:term-three-for-use-right-now} implies that"

Assessment: nearly identical sentence skeleton.

3. `lem:from-H-to-G`

Blueprint:
> "Iterating \ref{eq:i-think-this-is-what-i'm-supposed-to-prove} for `\ell=1,\dots,k` produces the Bernoulli polynomial"

Paper:
> "If we then repeatedly apply \Cref{eq:i-think-this-is-what-i'm-supposed-to-prove} for `\ell = 1, \ldots, k`,"

And later:

Blueprint:
> "The omitted Cauchy--Schwarz bound reuses the first square root from \ref{eq:call-again-later-part-dos} and the second square root from \ref{eq:call-again-later-part-tres}."

Paper:
> "The expression inside the first is equal to the expression inside the first square root in~\Cref{eq:call-again-later-part-dos}, ... The expression inside the second square root is equal to the expression inside the second square root in~\Cref{eq:call-again-later-part-tres}, ..."

Assessment: this proof is not verbatim line-for-line, but it is still very close to the paper's proof transcript rather than a blueprint sketch.

Suggested fix:
- Rewrite the two long proofs (`lem:commutativity-switcheroo`, `lem:from-H-to-G`) as actual sketches:
  - name the key intermediate comparison,
  - say which commuting / Cauchy-Schwarz lemmas are used,
  - summarize the iteration or telescoping step,
  - state that the paper's arithmetic gives the final exponent bookkeeping.
- Keep labels only for the specific equations later referenced by Lean-faithful sketches.

### 2. Proof sketch quality

Proof-by-proof audit:

| Proof | Verdict | Notes |
|---|---|---|
| `thm:ld-pasting` | Good sketch | Concise construction of a full measurement from the submeasurement and short consistency estimate. |
| `lem:ld-gbcon` | Good sketch | Trivial lemma; one-line "this is exactly `eq:ld-gbcon`" is sufficient. |
| `lem:ld-pasting-sub-measurement` | Good sketch | Short proof, names the key lemma and error absorption. |
| `prop:ld-dnoteq` | Good sketch | Short union-bound proof. |
| `lem:looks-easy-but-took-me-a-while` | Good sketch | Trivial scalar estimate; one sentence is enough. |
| `lem:g-complete-self-consistency` | Good sketch | Compact, names the equivalence and the norm-square identity. |
| `cor:g-bot-self-consistency` | Good sketch | Immediate from `I-G`. |
| `lem:commutativity-switcheroo` | Bad: too detailed / paper-proof-like | 89 nonblank proof lines; expands all four terms and runs multiple labeled transport steps. |
| `cor:commuting-with-G-complete` | Acceptable but still close to paper | Shorter than paper, but still very paper-shaped. |
| `cor:commuting-with-G-incomplete` | Good sketch | Reduction to complete-part commutation. |
| `cor:G-hat-facts` | Good sketch | Splits into cases and summarizes the error sum. |
| `lem:commute-g-half-sandwich` | Good sketch | Exactly the sort of "repeatedly commute and sum errors" summary a blueprint wants. |
| `lem:ld-sandwich-line-one-point` | Bad: too detailed | 54 nonblank lines, multiple labeled Cauchy-Schwarz steps. |
| `lem:h-b-consistency` | Bad: too detailed | 37 nonblank lines; still a derivation transcript rather than a sketch. |
| `lem:over-all-outcomes` | Bad: too detailed | 87 nonblank lines; follows the paper's full restriction-removal proof. |
| `lem:truncated-type-sum-recurrence` | Good sketch | Short structural argument. |
| `lem:from-H-to-G` | Bad: worst offender | 264 nonblank lines; essentially a condensed paper proof, not a sketch. |
| `lem:chernoff-bernoulli-matrix` | Borderline; should be shorter | It is mathematically clean, but still more detailed than needed for a standard probabilistic estimate. |
| `cor:ld-pasting-N-completeness` | Good sketch | Clear composition of three ingredients. |

Bad-proof evidence and fixes:

1. `lem:commutativity-switcheroo`

Quoted blueprint text:
> "For the first term in \ref{eq:g-commute-with-gg-error}, ... For the second term, ... For the third term, first ... Finally ..."

Why this is bad:
- This is a full proof transcript with all four terms expanded.
- It is much closer to the paper proof than to a 1-5 sentence blueprint sketch.

Suggested fix:
- Replace with 4-5 sentences:
  - expand the commutator norm into four terms,
  - compare each term to `\bra{\psi} G \ot M \ket{\psi}` using `prop:switch-sandwich`,
  - for the mixed term, commute one `G_g^x` across the sandwich using the assumed `\chi`-commutation and strong self-consistency,
  - sum the four errors.

2. `lem:ld-sandwich-line-one-point`

Quoted blueprint text:
> "The Cauchy--Schwarz argument uses `eq:add-in-the-bot` ... A second Cauchy--Schwarz step gives `eq:even-bigger-CS` ..."

Why this is bad:
- Too many intermediate displayed equations for a blueprint sketch.
- The proof reproduces the mechanics rather than summarizing the strategy.

Suggested fix:
- Keep only:
  - sum out the irrelevant coordinates,
  - commute `\widehat G_{g_i}^{x_i}` to the front using `lem:commute-g-half-sandwich`,
  - collapse the middle sandwich by summing over the earlier outcomes,
  - invoke `lem:ld-gbcon` for the final inconsistency bound.

3. `lem:h-b-consistency`

Quoted blueprint text:
> "If `|w|\ge d+1` and `f \ne h|_u`, then some active coordinate `i` must satisfy `g_i \ne \bot` and `g_i(u)\ne f(x_i)`."

Why this is only partly sketch-like:
- The main idea is stated clearly, but the proof still walks line-by-line through the expansion and distinct-to-independent reduction.

Suggested fix:
- Compress to:
  - expand `H` into tuples of slice outcomes,
  - observe any disagreement with `f` must show up on at least one active coordinate,
  - switch to distinct tuples using `prop:ld-dnoteq`,
  - sum the one-coordinate inconsistency bound from `lem:ld-sandwich-line-one-point`.

4. `lem:over-all-outcomes`

Quoted blueprint text:
> "We now remove the restriction to globally consistent tuples ... We next insert an indicator recording consistency along the sampled line ..."

Why this is bad:
- This is still the full paper proof plan with all intermediate transforms.
- It is not as long as the paper, but it is still much more than a sketch.

Suggested fix:
- Reduce to:
  - rewrite the sum over `H_h` as a sum over globally consistent tuples,
  - show inconsistent tuples contribute little by inserting line-consistency indicators,
  - bound the indicator probability by Schwartz–Zippel,
  - replace distinct tuples by independent tuples at cost `O(k^2/q)`.

5. `lem:from-H-to-G`

Quoted blueprint text:
> "The main iterative step is that for each `1\le \ell \le k`, ... `eq:i-think-this-is-what-i'm-supposed-to-prove` ..."

and later

> "We now prove `eq:i-think-this-is-what-i'm-supposed-to-prove-2}`. Writing `\widehat H` as a sandwich of `\widehat G` operators ... The corresponding Cauchy--Schwarz bound is ... Next, commute ... Continue commuting ... Finally move ..."

Why this is bad:
- This is far beyond sketch level.
- It is the closest thing in either chapter to a blueprint-proof copy of the paper.
- It recreates the paper's multi-stage transport argument almost in full.

Suggested fix:
- Replace by a high-level sketch:
  - define the truncated prefix sums `S_{\tau_{\ge \ell}}`,
  - state the one-step recurrence that removes coordinate `\ell`,
  - explain that the step uses self-consistency of `\widehat G`, commuting the leftmost factor through the half-sandwich, and the recurrence for `S`,
  - say that iterating over `\ell=1,\dots,k` yields the Bernoulli polynomial in `G`.

6. `lem:chernoff-bernoulli-matrix`

Quoted blueprint text:
> "Equivalently, `\E_{i\sim\mu}(1-\lambda_i)\le \kappa`, so Markov's inequality gives ..."

Why this is borderline:
- The proof is standard and faithful, but still more detailed than blueprint style usually needs.

Suggested fix:
- Compress to:
  - diagonalize `X` in the reduced state,
  - convert the claim to a scalar Bernoulli tail bound under the induced spectral distribution,
  - use Markov to show most mass lies above `\theta`,
  - apply Chernoff and the assumption `k \ge 2d/\theta`.

### 3. Label coverage

Counts:
- Paper labels: 84
- Blueprint labels: 93
- Missing paper labels in blueprint: 0

Conclusion:
- No paper labels are missing.

Extra blueprint labels not present in the paper:
- `chap:pasting`
- `def:G-hat`
- `def:distinct-tuples`
- `def:outcomes-by-type`
- `def:pasted-measurement`
- `def:truncated-type-sums`
- `def:types`
- `lem:ld-gbcon`
- `lem:truncated-type-sum-recurrence`

This is good: the blueprint adds helper definitions / lemmas, but it does not lose paper labels.

### 4. Equation labels in proofs

Result:
- No misplacement issue found.
- For every shared `eq:` label between paper and blueprint, the proof-vs-statement placement matches in this chapter.

Comment:
- Statement-level labels such as `eq:ld-abcon`, `eq:ld-gbcon`, `eq:ld-nu1-def`, `eq:quote-com-main`, `eq:M-self-consistent`, and `eq:M-commutes-with-G` are intentionally part of theorem setup or lemma hypotheses, not misplaced proof equations.

### 5. `\uses{}` in proof vs statement

This chapter has a real issue: many proof dependencies are still attached to the statement block instead of the proof block.

Correct proof-level `\uses{}` already inside proofs:
- `blueprint/src/chapter/ch09_pasting.tex:53`
- `blueprint/src/chapter/ch09_pasting.tex:153`

Misplaced statement-level `\uses{}` that are actually proof dependencies:

1. `blueprint/src/chapter/ch09_pasting.tex:119`
> `\uses{prop:simeq-to-approx, prop:triangle-inequality-for-approx_delta, prop:triangle-sub}`

Fix:
- Move this entire `\uses{...}` line into the proof of `lem:ld-gbcon`, or drop it entirely since the proof is one line.

2. `blueprint/src/chapter/ch09_pasting.tex:275`
> `\uses{prop:two-notions-of-self-consistency}`

Fix:
- Move into the proof of `lem:g-complete-self-consistency`.

3. `blueprint/src/chapter/ch09_pasting.tex:301`
> `\uses{lem:g-complete-self-consistency}`

Fix:
- Move into the proof of `cor:g-bot-self-consistency`.

4. `blueprint/src/chapter/ch09_pasting.tex:317`
> `\uses{prop:switch-sandwich}`

Fix:
- Move into the proof of `lem:commutativity-switcheroo`.

5. `blueprint/src/chapter/ch09_pasting.tex:427`
> `\uses{thm:com-main, lem:commutativity-switcheroo, lem:g-complete-self-consistency}`

Fix:
- Move into the proof of `cor:commuting-with-G-complete`.

6. `blueprint/src/chapter/ch09_pasting.tex:465`
> `\uses{cor:commuting-with-G-complete}`

Fix:
- Move into the proof of `cor:commuting-with-G-incomplete`.

7. `blueprint/src/chapter/ch09_pasting.tex:487`
> `\uses{lem:g-complete-self-consistency, cor:g-bot-self-consistency, cor:commuting-with-G-complete, cor:commuting-with-G-incomplete}`

Fix:
- Move into the proof of `cor:G-hat-facts`.

8. `blueprint/src/chapter/ch09_pasting.tex:518`
> `\uses{cor:G-hat-facts, prop:triangle-inequality-for-approx_delta}`

Fix:
- Move into the proof of `lem:commute-g-half-sandwich`.

9. `blueprint/src/chapter/ch09_pasting.tex:541`
> `\uses{lem:commute-g-half-sandwich, lem:ld-gbcon}`

Fix:
- Move into the proof of `lem:ld-sandwich-line-one-point`.

10. `blueprint/src/chapter/ch09_pasting.tex:615`
> `\uses{def:pasted-measurement, prop:ld-dnoteq, lem:ld-sandwich-line-one-point}`

Fix:
- Keep `def:pasted-measurement` on the statement if desired.
- Move `prop:ld-dnoteq` and `lem:ld-sandwich-line-one-point` into the proof.

11. `blueprint/src/chapter/ch09_pasting.tex:675`
> `\uses{def:outcomes-by-type, prop:ld-dnoteq, lem:ld-sandwich-line-one-point, lem:schwartz-zippel-individual}`

Fix:
- Keep `def:outcomes-by-type` on the statement.
- Move the three proof dependencies into the proof.

12. `blueprint/src/chapter/ch09_pasting.tex:810`
> `\uses{cor:G-hat-facts, lem:commute-g-half-sandwich, def:pasted-measurement, def:truncated-type-sums, lem:truncated-type-sum-recurrence}`

Fix:
- Keep at most the definitional dependencies needed to parse the statement.
- Move `cor:G-hat-facts`, `lem:commute-g-half-sandwich`, and `lem:truncated-type-sum-recurrence` into the proof.

13. `blueprint/src/chapter/ch09_pasting.tex:1150`
> `\uses{lem:over-all-outcomes, lem:from-H-to-G, lem:chernoff-bernoulli-matrix}`

Fix:
- Move this entire line into the proof of `cor:ld-pasting-N-completeness`.

Net conclusion for `ch09`:
- Proof-level `\uses` are not consistently inside proofs.
- This is currently the most systematic style-guide violation in the chapter.

## Chapter 07: `ch07_self_improvement`

### 1. Copy-paste ratio

Rough estimate:
- Verbatim or near-verbatim from paper: about 45% to 55%
- Genuinely rewritten / compressed: about 45% to 55%

Lower bound from exact normalized line overlap:
- 83 / 422 nonempty blueprint lines = 19.7%

Why this chapter scores higher than `ch09`:
- The theorem and lemma statements are very close to the paper.
- The helper proof and `lem:add-in-u` keep much of the paper's displayed derivation structure.
- The blueprint does improve structure by placing the long "proof of each item" derivation inside actual `proof` environments.

Concrete near-copy passages:

1. `lem:self-improvement-helper` statement

Blueprint:
> "Let `G \in \polymeas{m}{q}{d}` be a measurement with the following property:"

Paper:
> "Let `G \in \polymeas{m}{q}{d}` be a measurement with the following property:"

And the four-item conclusion is also very close throughout.

2. `lem:add-in-u`

Blueprint:
> "To show this, we bound the magnitude of the difference:"

Paper:
> "To show this, we bound the magnitude of the difference."

This exact sentence is reused repeatedly in the same proof pattern.

3. End of `lem:add-in-u`

Blueprint:
> "The same Cauchy--Schwarz estimate as in~\eqref{eq:change-one-cauchy-schwarz}, with the final copy of `A^v_{h(v)}` replaced by `A^u_{h(u)}`, gives the same bound `\sqrt{\zeta_{\mathrm{variance}}}` because the first factor is again at most~`1` and the second is again controlled by Lemma~\ref{lem:global-variance-of-points}. Summing the four transports gives an error of `2\sqrt{2\delta} + 2\sqrt{\zeta_{\mathrm{variance}}}`, and the lemma follows from `2\delta \leq \zeta_{\mathrm{variance}}`."

Paper:
> "As for the term inside the second square root, it is equal to the term inside the first square root in \Cref{eq:change-one-cauchy-schwarz}, which we showed was at most `\zeta_{\mathrm{variance}}`. This concludes the proof with an error of `2\sqrt{2\delta} + 2\sqrt{\zeta_{\mathrm{variance}}}`. The lemma now follows by observing that `2\delta \leq \zeta_{\mathrm{variance}}`."

Assessment: not exact copy, but clearly a very close rewrite of the same proof transcript.

Suggested fix:
- Rework `lem:self-improvement-helper`, `lem:sdp`, and especially `lem:add-in-u` into actual sketches that cite the key transforms and state the error bookkeeping without replaying each Cauchy-Schwarz step.

### 2. Proof sketch quality

Proof-by-proof audit:

| Proof | Verdict | Notes |
|---|---|---|
| `lem:self-improvement-helper` | Bad: too detailed / near proof transcript | 201 nonblank proof lines; the four item-proofs are spelled out in derivation form. |
| `lem:sdp` | Bad: too detailed | 47 nonblank lines; still a full canonical-form duality proof rather than a sketch. |
| `lem:add-in-u` | Bad: too detailed / close to paper | 54 nonblank lines, four separate transport steps, repeated Cauchy-Schwarz derivations. |
| `thm:self-improvement` | Mostly a meaningful sketch | It clearly says: apply helper, orthonormalize, then transfer the four conclusions one by one. Still longer than ideal, but much better than the three proofs above. |

Bad-proof evidence and fixes:

1. `lem:self-improvement-helper`

Quoted blueprint text:
> "We first move the leftmost copy of `A^u_a` across the bipartition ... We next remove the remaining copy of `A^u_a` on Bob's side ..."

Why this is bad:
- This is a proof transcript, not a sketch.
- It reproduces intermediate labels and transport steps in detail.

Suggested fix:
- Break it into four 3-5 sentence item-sketches:
  - completeness: define `H` using the SDP optimizer and compare `\sum_h H_h` to `Z`;
  - `A`-consistency: apply `lem:add-in-u` to the inconsistency expression and use projectivity;
  - self-consistency: use the sandwiched identities `eq:h-sandwich` and `eq:h-blt`, then enlarge to all pairs and control the off-diagonal part;
  - boundedness: combine the previous `A`-consistency bound with `eq:gonna-use-this-later-H-versus-Z`.

2. `lem:sdp`

Quoted blueprint text:
> "Rewrite `\eqref{eq:primal-objective}` in canonical block form. Let `r` be the dimension ... fix an ordering `g_1,\ldots,g_M` ..."

Why this is bad:
- It gives the full block-matrix setup, rather than a blueprint-style summary.

Suggested fix:
- Replace with:
  - rewrite the primal in standard block-diagonal SDP form,
  - identify the dual variable with a single PSD matrix `Z`,
  - use Slater for strong duality,
  - translate complementary slackness back to `T_g(Z-A_g)=0` and `\sum_g T_g=I`.

3. `lem:add-in-u`

Quoted blueprint text:
> "To show this, we bound the magnitude of the difference:"

and later

> "The same Cauchy--Schwarz estimate as in~\eqref{eq:change-one-cauchy-schwarz} ... Summing the four transports gives an error ..."

Why this is bad:
- The proof is still organized exactly like the paper's four transport steps.
- It is faithful, but not a sketch.

Suggested fix:
- Summarize as:
  - expand `H_h` as the average of the sandwiched operators,
  - move the two copies of `A^{v}_{h(v)}` across the tensor factor using self-consistency of `A`,
  - replace `A^v_{h(v)}` by `A^u_{h(u)}` using global variance,
  - collect the four transport errors into `O(\sqrt{\delta}+\sqrt{\zeta_{\mathrm{variance}}})`.

### 3. Label coverage

Counts:
- Paper labels: 56
- Blueprint labels: 57
- Missing paper labels in blueprint: 0

Conclusion:
- No paper labels are missing.

Extra blueprint label:
- `chap:self-improvement`

### 4. Equation labels in proofs

Result:
- No blueprint misplacement issue found.
- In fact, the blueprint improves on the paper here.

Important detail:
- 21 shared `eq:` labels that were outside any `proof` environment in the paper now sit inside an actual `proof` environment in the blueprint.

Examples:
- `eq:Z-greater-than-A`
- `eq:swap-Z-for-A`
- `eq:bracketize-the-expression`
- `eq:consistency-with-A-baby-step`
- `eq:self-consistency-baby-step`
- `eq:threw-in-h-prime`
- `eq:swap-u-for-v-attack-of-the-clones`

Appropriate statement-level equation labels that remain outside proofs:
- `eq:primal-objective`
- `eq:dual-objective`
- `eq:dual-constraint`
- `eq:slater`

These belong to the lemma statement and are correctly placed.

### 5. `\uses{}` in proof vs statement

Correct proof-level `\uses{}` already inside proofs:
- `blueprint/src/chapter/ch07_self_improvement.tex:48`
- `blueprint/src/chapter/ch07_self_improvement.tex:456`

One clear misplaced statement-level `\uses{}`:

1. `blueprint/src/chapter/ch07_self_improvement.tex:338`
> `\uses{lem:global-variance-of-points, prop:simeq-to-approx}`

Why this is an issue:
- These are proof dependencies for `lem:add-in-u`, not statement dependencies.

Fix:
- Move this entire `\uses{...}` line into the proof of `lem:add-in-u`.

The remaining statement-level `\uses` in this chapter are mostly definitional and look reasonable.

## Prioritized fixes

1. Move proof-only `\uses{}` out of statement blocks, especially throughout `ch09_pasting`.

2. Compress the longest proofs into actual sketches:
- `lem:from-H-to-G`
- `lem:over-all-outcomes`
- `lem:commutativity-switcheroo`
- `lem:self-improvement-helper`
- `lem:add-in-u`
- `lem:sdp`

3. Reduce copy-paste pressure in the most paper-shaped passages by rewriting the argument structure in blueprint voice instead of replaying the paper's step-by-step derivation.

## Bottom line

Good news:
- No paper labels are missing in either chapter.
- Equation labels are not misplaced at statement level; `ch07_self_improvement` is actually structurally cleaner than the paper on this point.

Main problems:
- The long proofs are often still too detailed to count as blueprint sketches.
- `ch09_pasting` has a systematic `\uses{}` placement problem: many proof dependencies are still attached to statements.
