# Outline for branch `fix-processedg-sorries`

Target: `MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean`

Goal: eliminate the remaining `sorry` in `evaluatedSlice_scalar_chain_bound`, and hence remove all `sorry`s from the target file.

## Paper fragment

From `references/ldt-paper/commutativity-G.tex` (around lines 72–131):

```tex
To begin, we note that for each $(u, x) \in \F_q^{m+1}$,
\begin{equation}\label{eq:sum-of-gux}
G^{u, x} = \sum_a G^{u, x}_a =  \sum_a G^{x}_{[g(u) = a]} = G^x.
\end{equation}
As a result,
 \Cref{item:data-processed-consistency} and \Cref{prop:cons-sub-meas} imply that
\begin{align}
G^{u,x}_a \ot I 
&\approx_{4\zeta} G^{u, x} \otimes A^{u, x}_a \nonumber\\
&= G^{x} \otimes A^{u, x}_a, \label{eq:add-an-a}
\end{align}
where the second step is by \Cref{eq:sum-of-gux}.
We can therefore approximate the second term of \Cref{eq:gcom8}
as
\begin{align}
&\E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\bu,\bx}_a G^{\bv,\by}_b  \ot I \ket{\psi} \nonumber\\
\approx_{2\sqrt{\zeta}}& \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\bu,\bx}_a G^{\by}  \ot A^{\bv,\by}_b \ket{\psi}.\label{eq:apply-add-an-a-once}
\end{align}
using \Cref{prop:closeness-of-ip} and \Cref{eq:add-an-a}.
Next, we claim that
\begin{equation}
\eqref{eq:apply-add-an-a-once}
\approx_{\sqrt{\zeta}}\E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\bu,\bx}_a  \ot A^{\bv,\by}_b \ket{\psi}. \label{eq:gcom9}
\end{equation}
This is proved in \Cref{clm:g-comm-stability} below. Continuing, we have
\begin{align}
\eqref{eq:gcom9} &\approx_{2\sqrt{\zeta}} \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\bx}  \ot A^{\bv,\by}_b A^{\bu,\bx}_a \ket{\psi} \nonumber\\
&\approx_{6\sqrt{\gamma (m+1)}} \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b  G^{\bx}  \ot A^{\bu,\bx}_a A^{\bv,\by}_b \ket{\psi}. \label{eq:dunno-what-i-should-call-this}
\end{align}
The first approximation again uses  \Cref{prop:closeness-of-ip} and \Cref{eq:add-an-a}. The second approximation follows from  \Cref{prop:closeness-of-ip} and \Cref{thm:commutativity-points}.
Next, we claim that
\begin{equation}
\eqref{eq:dunno-what-i-should-call-this}
\approx_{\sqrt{\zeta}+6\sqrt{\gamma(m+1)}} \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu, \bx}_a  G^{\bv,\by}_b \ot A^{\bu,\bx}_a  A^{\bv,\by}_b \ket{\psi}.
\label{eq:gcom10}
\end{equation}
This is proved in \Cref{clm:g-comm-stability2} below.
We now apply \Cref{eq:add-an-a} twice with the help of \Cref{prop:closeness-of-ip}.
\begin{align}
\eqref{eq:gcom10}
&= \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bx}G^{\bu, \bx}_a  G^{\bv,\by}_b \ot A^{\bu,\bx}_a  A^{\bv,\by}_b \ket{\psi} \tag{because~$G$ is projective}\nonumber\\
&\approx_{2\sqrt{\zeta}} \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi}G^{\bu,\bx}_a G^{\bu,\bx}_a  G^{\bv,\by}_b \ot A^{\bv,\by}_b \ket{\psi} \nonumber\\
&= \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b \ot A^{\bv,\by}_b \ket{\psi} \tag{because~$G$ is projective}\nonumber\\
&= \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\by} \ot A^{\bv,\by}_b \ket{\psi} \tag{because~$G$ is projective}\nonumber\\
&\approx_{2\sqrt{\zeta}} \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\bv, \by}_b \ot I \ket{\psi}. \label{eq:gonna-cite-this-in-just-a-bit}
\end{align}
Now, \Cref{item:data-processed-self-consistency} and the fact that~$G$ is projective allows us to apply \Cref{prop:two-notions-of-self-consistency}, which states that~$G$ is $\zeta/2$-strongly self-consistent. Hence, \Cref{prop:two-notions-of-self-consistency-after-evaluation} says that we can ``post-process'' its measurement outcomes:
\begin{equation*}
G^x_{[g(u)=a]} \ot I \approx_{\zeta} I \ot G^x_{[g(u)=a]}.
\end{equation*}
In other words, using our abbreviation,
\begin{equation}\label{eq:new-fact-that-i-derived}
G^{u,x}_a \ot I \approx_{\zeta} I \otimes G^{u,x}_a.
\end{equation}
Applying \Cref{eq:new-fact-that-i-derived} twice with the help of \Cref{prop:closeness-of-ip},
we conclude that
\begin{align*}
\eqref{eq:gonna-cite-this-in-just-a-bit}
&\approx_{\sqrt{\zeta}} \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b  \ot G^{\bv, \by}_b \ket{\psi}\\
&\approx_{\sqrt{\zeta}} \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bv, \by}_b G^{\bu,\bx}_a  G^{\bv,\by}_b  \ot I \ket{\psi}.
\end{align*}
```

## Lean-side decomposition

The target theorem already has the last postprocessed SSC ingredient available as
`evaluatedSlice_phaseEightNine_tail_bound`.  The missing assembly should be split into the same paper phases.

### Existing ingredients already in the repo

- `evaluatedPointSelfConsistency_fst`
- `evaluatedPointSelfConsistency_snd`
- `evaluatedSlice_phaseOne_insert_bound`
- `evaluatedSlice_phaseThree_insert_bound`
- `evaluatedSlice_phaseFour_pointSwap_bound`
- `evaluatedSlice_phaseTwo_scalar_rewrite`
- `evaluatedSlice_phaseFive_scalar_rewrite`
- `gCommStability_overlap`
- `gCommStabilityTwo_overlap`
- `evaluatedSlice_phaseEightNine_tail_bound`
- `evaluatedSliceCommutation_qSDDOp_avg_eq`

### Missing assembly pieces to expose in `ProcessedG.lean`

1. Build the `consSubMeas`-derived combined controls on the first and second evaluated points.
2. Define the phase-1 inserted scalar expression and invoke `evaluatedSlice_phaseOne_insert_bound`.
3. Introduce a local phase-2 helper that rewrites the inserted `G^y`-weighted term to the stability-one `SDDOpRel` family and then applies `gCommStability_overlap`.
4. Define the phase-3 inserted scalar expression and invoke `evaluatedSlice_phaseThree_insert_bound`.
5. Introduce a local phase-4 helper that packages the swapped middle term and applies `evaluatedSlice_phaseFour_pointSwap_bound`.
6. Introduce a local phase-5 helper that rewrites the post-swap `G^x`-weighted term to the stability-two family and then applies `gCommStabilityTwo_overlap`.
7. Combine the phase bounds by repeated triangle inequalities and simple ring bookkeeping.
8. Finish with the arithmetic inequality
   `2 * (6 * sqrt zeta + 6 * sqrt zeta + 12 * sqrt (gamma * (m+1))) ≤ commDataProcessedGError ...`.

## Immediate coding plan

First, replace the single terminal `sorry` in `evaluatedSlice_scalar_chain_bound` by a structured scaffold:

- local `let` bindings for the scalar averages in each paper line,
- `have` statements named by phase,
- if needed, small local helper lemmas with temporary `sorry`s for phase 2 / phase 4 / phase 5 / final arithmetic.

Then eliminate the temporary `sorry`s one by one in the order:

1. phase-2 rewrite + `gCommStability_overlap`,
2. phase-4 swap via `evaluatedSlice_phaseFour_pointSwap_bound`,
3. phase-5 rewrite + `gCommStabilityTwo_overlap`,
4. triangle-inequality assembly,
5. final error arithmetic.
