# Chapter 3 Gap Analysis: Preliminaries

## Scope

Files read:

- `references/ldt-paper/preliminaries.tex` (`1177` lines)
- `blueprint/src/chapter/ch03_preliminaries.tex` (`338` lines)
- `MIPStarRE/LDT/Preliminaries/Defs.lean`
- `MIPStarRE/LDT/Preliminaries/Theorems.lean`

Headline result:

- The paper chapter has `47` labels; the blueprint chapter has `30`.
- The six paper labels you identified are genuinely absent from the blueprint:
  `prop:fourier-fact-scalar`, `prop:fourier-fact-vector`,
  `lem:schwartz-zippel-total-degree`,
  `prop:easy-approx-from-approx-delta`, `prop:cab-approx-delta`,
  `prop:cool-prop`.
- Of those six, none has a direct named Lean theorem in `MIPStarRE/LDT/Preliminaries/`.
- Two of them have meaningful nearby Lean surrogates:
  `prop:fourier-fact-vector` is partially reflected later in the expansion chapter, and
  `prop:cool-prop` is effectively inlined into the completion proof infrastructure.

## Shared-label mismatch check

I compared the shared proposition/lemma labels between the paper and blueprint. I found one clearly significant statement drift:

### `prop:closeness-of-ip`

Paper statement:

- Has two separate clauses.
- The second clause is not just "the analogous right-sided statement":
  it assumes `(A_a^x)^\dagger \approx_\gamma (B_a^x)^\dagger`
  and the different normalization condition
  `\sum_a (\sum_b C^x_{a,b})^\dagger (\sum_b C^x_{a,b}) \le I`.

Blueprint statement:

- States the first clause explicitly.
- Then says only: "The analogous statement also holds when the `C_{a,b}^x` act on the right."

Assessment:

- This is a real weakening / compression of the formal statement.
- If the blueprint is meant to be theorem-faithful, it should spell out the daggered right-action variant exactly as in the paper.

Other than that, the shared labels are mostly faithful restatements, usually just shorter or more notation-normalized.

## Missing-label details

### 1. `prop:fourier-fact-scalar`

Exact paper statement:

```latex
\begin{proposition}
\label{prop:fourier-fact-scalar}
Let $a \in \F_q$. Then
\begin{equation*}
\E_{\bx \sim \F_q} \omega^{\tr[\bx \cdot a]}
= \left\{\begin{array}{rl}
	1 & \text{if $a = 0$},\\
	0 & \text{otherwise}.
	\end{array}\right.
\end{equation*}
\end{proposition}
```

Where it is used in the paper:

- `references/ldt-paper/preliminaries.tex:82`
  used in the proof of `prop:fourier-fact-vector`.
- `references/ldt-paper/expansion.tex:95`
  used in the Fourier-eigenvalue computation in the expansion chapter.

Lean status:

- No direct theorem or definition in `MIPStarRE/LDT/Preliminaries/`.
- No direct scalar finite-field trace orthogonality theorem found elsewhere in the repo.
- The closest related later artifact is the hard-coded Fourier orthogonality surrogate
  `fourierBasisInnerProduct` and `eigenvectors.orthonormality` in
  `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean:516-567`,
  but that bypasses this scalar lemma entirely.

Estimated difficulty:

- `easy`
- Reason: mathematically elementary, but it still needs finite-field trace and additive-character setup in Lean.

### 2. `prop:fourier-fact-vector`

Exact paper statement:

```latex
\begin{proposition}
\label{prop:fourier-fact-vector}
Let $v \in \F_q^m$. Then
\begin{equation*}
\E_{\bu \sim \F_q^m} \omega^{\tr[\bu \cdot v]}
= \left\{\begin{array}{rl}
	1 & \text{if $v = 0$},\\
	0 & \text{otherwise}.
	\end{array}\right.
\end{equation*}
\end{proposition}
```

Where it is used in the paper:

- `references/ldt-paper/expansion.tex:71`
  used in the main Fourier-basis orthogonality computation for the expansion chapter.

Lean status:

- No direct theorem in `MIPStarRE/LDT/Preliminaries/`.
- Partial surrogate later:
  `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean:516-567`
  defines
  `fourierBasisInnerProduct params α β := if α = β then 1 else 0`
  and packages that as `eigenvectors.orthonormality`.
- This is only a later scaffolded endpoint, not a formal derivation from the paper proposition.

Estimated difficulty:

- `easy`
- Reason: once the scalar orthogonality fact exists, this should be a short product-factorization argument.

### 3. `lem:schwartz-zippel-total-degree`

Exact paper statement:

```latex
\begin{lemma}[Schwartz–Zippel lemma~\cite{Sch80,Zip79}]\label{lem:schwartz-zippel-total-degree}
Let $g, h:\F_q^m \rightarrow \F_q$ be two distinct polynomials of total degree~$d$.
Then
\begin{equation*}
\Pr_{\bx \sim \F_q^m}[g(\bx) = h(\bx)] \leq \frac{d}{q}.
\end{equation*}
\end{lemma}
```

Where it is used in the paper:

- `references/ldt-paper/preliminaries.tex:116`
  used immediately to derive the individual-degree corollary.
- I found no later cross-chapter references to this label.

Lean status:

- No direct theorem in `MIPStarRE/LDT/Preliminaries/` or elsewhere in the repo.
- The repo does already model low-individual-degree polynomials in
  `MIPStarRE/LDT/Basic/Parameters.lean`,
  but there is no total-degree Schwartz–Zippel theorem.
- The blueprint keeps only the corollary
  `lem:schwartz-zippel-individual`,
  proved by appealing informally to this missing stronger lemma.

Estimated difficulty:

- `hard`
- Reason: this is the first genuinely nontrivial algebraic lemma among the six, and formalizing the multivariate total-degree bound over finite fields is likely substantial.

### 4. `prop:easy-approx-from-approx-delta`

Exact paper statement:

```latex
\begin{proposition}\label{prop:easy-approx-from-approx-delta}
Let $A = \{A^x_a\}$, $B = \{B^x_a\}$, and $C = \{C^x_a\}$ be sub-measurements
such that $A^x_a \approx_{\delta} B^x_a$. Then
\begin{equation*}
\E_{\bx} \sum_a \bra{\psi} A^{\bx}_a  C^{\bx}_a \ket{\psi}
\approx_{\sqrt{\delta}} \E_{\bx} \sum_a \bra{\psi} B^{\bx}_a  C^{\bx}_a \ket{\psi}.
\end{equation*}
\end{proposition}
```

Where it is used in the paper:

- `references/ldt-paper/preliminaries.tex:858`
  first use in `prop:completeness-transfer-projective-P`.
- `references/ldt-paper/preliminaries.tex:860`
  second use in the same proof.
- `references/ldt-paper/preliminaries.tex:1019`
  first use in `prop:completeness-transfer-self-consistent-A`.
- `references/ldt-paper/preliminaries.tex:1021`
  second use in the same proof.
- `references/ldt-paper/preliminaries.tex:1070`
  used in `prop:self-consistency-implies-data-processing`.
- `references/ldt-paper/preliminaries.tex:1162`
  used in the proof of `prop:completing-to-measurement`.
- `references/ldt-paper/self_improvement.tex:751`
  used again in the self-improvement chapter.

Lean status:

- No direct public theorem with this name or statement in `MIPStarRE/LDT/Preliminaries/`.
- Closest internal surrogates:
  `question_overlap_gap_left` at
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:1008-1085`
  and
  `question_overlap_gap_right` at
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:1086-1159`.
- Those private lemmas are exactly the same Cauchy-Schwarz pattern specialized to overlap expressions like
  `\sum_a \langle \psi, A_a A_a \psi \rangle`,
  `\sum_a \langle \psi, A_a B_a \psi \rangle`,
  and
  `\sum_a \langle \psi, B_a B_a \psi \rangle`.
- The completion proof at
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:3014-3037`
  already uses these private bounds in place of a public `prop:easy-approx-from-approx-delta`.

Estimated difficulty:

- `medium`
- Reason: the proof is short, but it wants a clean public API for repeated Cauchy-Schwarz overlap transfers.

### 5. `prop:cab-approx-delta`

Exact paper statement:

```latex
\begin{proposition}
  \label{prop:cab-approx-delta}
  Let $\{A^x_a\}, \{B^x_a\},$ and $\{C^x_{a,b}\}$ be
  matrices. Suppose that $A^{x}_a \approx_\delta B^{x}_a$ and that
  for all $x$ and $a$, $\sum_b (C^{x}_{a,b})^\dagger
  (C^{x}_{a,b}) \leq I$. Then
  \[ C^{x}_{a,b} A^x_{a} \approx_{\delta} C^{x}_{a,b} B^{x}_a. \]
\end{proposition}
```

Where it is used in the paper:

- `references/ldt-paper/expansion.tex:313`
  cited as one of the reusable approximation steps in the expansion proof.
- `references/ldt-paper/ld-pasting.tex:884`
  used in the low-degree pasting chapter.

Lean status:

- No direct theorem in `MIPStarRE/LDT/Preliminaries/` or elsewhere in the repo.
- Closest infrastructure:
  `qSDDOp` / `SDDOpRel` in
  `MIPStarRE/LDT/Test/Defs.lean:76-165`
  gives a raw-operator-family version of state-dependent distance.
- There is also a useful bounded-sandwich Cauchy-Schwarz helper,
  `sum_ev_mul_leftBounded_le_of_leftHermitian`, at
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:1161-1212`,
  but it is private and not the same proposition.

Estimated difficulty:

- `medium`
- Reason: mathematically straightforward once raw operator-family `≈` is set up, but it wants a clean general-purpose operator-family theorem rather than the current ad hoc helpers.

### 6. `prop:cool-prop`

Exact paper statement:

```latex
\begin{proposition}\label{prop:cool-prop}
Let $\ket{\psi}$ be a permutation-invariant state,
and let $A = \{A_a\}$ be a sub-measurement such that
\begin{equation*}
\E_{\bx} \sum_a \bra{\psi} A_a \otimes A_a \ket{\psi} \geq  \bra{\psi} A \otimes I \ket{\psi} - \zeta.
\end{equation*}
Then
\begin{equation*}
\sum_a \bra{\psi} (A_a)^2 \otimes I \ket{\psi} \geq \sum_a \bra{\psi} A_a \otimes I \ket{\psi} -\zeta.
\end{equation*}
\end{proposition}
```

Where it is used in the paper:

- `references/ldt-paper/preliminaries.tex:1167`
  used inside the proof of `prop:completing-to-measurement`.

Lean status:

- No direct public theorem with this name or exact statement.
- The blueprint functionally replaces it by two new helper lemmas:
  `lem:self-consistency-same-side-square`
  and
  `lem:completion-missing-mass-bound`.
- In Lean, the same content is largely inlined:
  `bipartiteSSC_implies_localSSC_liftLeft` at
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:2838-2974`
  bridges bipartite strong self-consistency to local square-based control, and
  `closenessAfterCompletion_core_local` at
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:3038-3052`
  derives the lower bound on the square mass of `A` that the paper isolates as `prop:cool-prop`.

Estimated difficulty:

- `medium`
- Reason: the argument is short on paper, but in the current Lean architecture it sits right on the interface between bipartite SSC, local SSC, and permutation invariance.

## Lean coverage summary for the six missing labels

Directly present as named Lean theorems in `MIPStarRE/LDT/Preliminaries/`:

- None.

Partially present as nearby infrastructure:

- `prop:fourier-fact-vector`
  partially mirrored by later expansion scaffolding:
  `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean:516-567`.
- `prop:easy-approx-from-approx-delta`
  partially subsumed by private overlap-gap lemmas:
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:1008-1159`.
- `prop:cool-prop`
  effectively inlined into the completion proof:
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:2838-3114`.

Not present even as a close named theorem:

- `prop:fourier-fact-scalar`
- `lem:schwartz-zippel-total-degree`
- `prop:cab-approx-delta`

## Suggested prioritization

If the goal is "close the paper-blueprint gap" rather than "formalize in proof dependency order", the cleanest order is:

1. `lem:schwartz-zippel-total-degree`
   because the blueprint currently proves the individual-degree corollary from an omitted stronger lemma.
2. `prop:easy-approx-from-approx-delta`
   because it is used repeatedly inside preliminaries and again in `self_improvement.tex`.
3. `prop:cab-approx-delta`
   because it is used across later chapters (`expansion.tex`, `ld-pasting.tex`).
4. `prop:cool-prop`
   because it clarifies the structure already hidden inside the completion proof.
5. `prop:fourier-fact-scalar`
6. `prop:fourier-fact-vector`

If the goal is instead "close the Lean formalization risk", I would move the Fourier pair later and prioritize the three reusable approximation lemmas plus Schwartz–Zippel first.
