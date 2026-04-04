# Chapter 7 Gap Analysis: Self-Improvement

## Executive summary

- Paper chapter: `references/ldt-paper/self_improvement.tex`
  - 813 lines
  - 56 paper labels
- Blueprint chapter: `blueprint/src/chapter/ch07_self_improvement.tex`
  - 130 lines
  - 5 blueprint labels
- Exact label overlap: 4 labels
  - `lem:self-improvement-helper`
  - `lem:sdp`
  - `lem:add-in-u`
  - `thm:self-improvement`
- Exact paper labels missing from blueprint: 52
- Lean chapter files:
  - `MIPStarRE/LDT/SelfImprovement/Defs.lean`
  - `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean`
  - `MIPStarRE/LDT/SelfImprovement/Theorems.lean`

The high-level picture is:

- The blueprint keeps the four top-level mathematical results, but drops almost all internal label structure:
  - both section labels,
  - all theorem item labels,
  - all SDP equation labels,
  - all proof-step equation labels.
- The Lean folder already contains a fairly rich scaffold:
  - explicit SDP operators and errors,
  - the sandwiched family `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`,
  - helper/projective boundedness operators,
  - matrix-level witness structures,
  - theorem statement structures.
- The actual proofs are still open:
  - `selfImprovementHelper` is `sorry`
  - `sdp` is `sorry`
  - `addInU` is `sorry`
  - `selfImprovement` is `sorry`

## Existing Lean surface

### Definitions already present

From `MIPStarRE/LDT/SelfImprovement/Defs.lean`:

- `averagedPointOperator`
  - formalizes `A_g = E_u A^u_{g(u)}`.
- `sdpPrimalObjective`, `sdpDualObjective`, `sdpDualSlackOperator`
  - formalize the SDP objective/slack operators.
- `sdpComplementarySlacknessEquation`
  - formalizes `T_g Z = T_g A_g`.
- `sandwichedPolynomialOutcomeOperatorAt`
  - formalizes `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`.
- `sandwichedPolynomialSubMeasAt`, `averagedSandwichedPolynomialSubMeas`
  - formalize pointwise and averaged `H`.
- `selfImprovementVarianceError`, `addInUError`,
  `selfImprovementHelperError`,
  `selfImprovementOrthogonalizationError`,
  `selfImprovementDataProcessingError`,
  `selfImprovementError`
  - formalize the chapter's bundled quantitative errors.

From `MIPStarRE/LDT/SelfImprovement/Theorems.lean`:

- `SdpOptimalPair`, `SdpStatement`
- `AddInUStatement`
- `SelfImprovementHelperConclusion`
- `SelfImprovementConclusion`
- `SelfImprovementSubMeasConclusion`
- `helperBoundednessGap`, `projectiveResidualOperator`, `projectiveBoundednessGap`

From `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean`:

- `MatrixSdpRealization`
- `MatrixSdpOptimalWitness`
- `MatrixAddInUTransferStatement`

### Proof status

`rg '\bsorry\b' MIPStarRE/LDT/SelfImprovement/*.lean` finds four unresolved proofs, all in `Theorems.lean`:

- `selfImprovementHelper`
- `sdp`
- `addInU`
- `selfImprovement`

So the Lean chapter is a strong statement scaffold, but not yet a proved formalization.

## A. Opening + helper lemma

### Label coverage

| Paper label | Kind | In blueprint? | Lean correspondence |
| --- | --- | --- | --- |
| `sec:self-improvement` | section label | No | none |
| `lem:self-improvement-helper` | lemma | Yes | `selfImprovementHelper` |
| `item:self-improvement-G-consistency` | item | No | hypothesis `hcons` of `selfImprovementHelper` |
| `item:self-improvement-completeness` | item | No | `SelfImprovementHelperConclusion.completeness` |
| `item:self-improvement-A-consistency` | item | No | `SelfImprovementHelperConclusion.pointConsistency` |
| `item:self-improvement-self` | item | No | `SelfImprovementHelperConclusion.strongSelfConsistency` |
| `item:self-improvement-boundedness` | item | No | `SelfImprovementHelperConclusion.helperResidualBound`, `bounded`, `dualDominatesAveragedPoint` |

Exact overlap in this block: only `lem:self-improvement-helper`.

### Exact missing statements

- `sec:self-improvement`
  - No mathematical statement; this is the opening section anchor for the whole non-projective stage.

- `item:self-improvement-G-consistency` (paper lines 28-31)
  ```tex
  \text{On average over } \bu \sim \F_q^{m}, \qquad
  A^{u}_a \otimes I \simeq_{\nu} I \otimes G_{[g(u)=a]}.
  ```

- `item:self-improvement-completeness` (paper lines 39-42)
  ```tex
  \text{If } H = \sum_h H_h, \text{ then } \qquad
  \bra{\psi} H \otimes I \ket{\psi} \geq (1-\nu)-\zeta.
  ```

- `item:self-improvement-A-consistency` (paper lines 43-46)
  ```tex
  \text{On average over } \bu \sim \F_q^m, \qquad
  A^u_a \otimes I \simeq_{\zeta} I \otimes H_{[h(u) = a]}.
  ```

- `item:self-improvement-self` (paper lines 47-50)
  ```tex
  \sum_{h} \bra{\psi} H_h \otimes H_h \ket{\psi}
  \geq \bra{\psi} H \otimes I \ket{\psi} - \zeta.
  ```

- `item:self-improvement-boundedness` (paper lines 51-58)
  ```tex
  \bra{\psi} Z \otimes I \ket{\psi}
    -\E_{\bu} \sum_a \bra{\psi}  A^{\bu}_{a} \otimes H_{[h(\bu)=a]} \ket{\psi}
    \leq \zeta
  ```
  and, for each `h in polyfunc`,
  ```tex
  Z \geq \left(\E_{\bu} A^{\bu}_{h(\bu)}\right).
  ```

### Dependency chain and proof structure

Paper:

1. Define the SDP from averaged point operators `A_g`.
2. Solve the SDP using `lem:sdp` to get optimal `T` and `Z`.
3. Define `H^u_h := A^u_{h(u)} T_h A^u_{h(u)}` and average to get `H_h`.
4. Use `lem:add-in-u` as the core transfer lemma.
5. Split the helper proof into four separate estimates:
   - completeness,
   - consistency with `A`,
   - strong self-consistency,
   - boundedness.

Lean:

1. `Defs.lean` already defines `A_g`, `H^u_h`, averaged `H`, and all bundled errors.
2. `Theorems.lean` packages the helper output as `SelfImprovementHelperConclusion`.
3. The wrapper theorem `selfImprovementHelper` is present but still `sorry`.

### Statement mismatches / compression notes

- Blueprint compression:
  - The helper theorem in the blueprint drops all item labels, so later proof references cannot target individual conclusions.
  - The blueprint rewrites the explicit paper formula for strong self-consistency into the definitional phrase "the family `H` is `zeta`-strongly self-consistent".
- This is mathematically reasonable, but it loses the exact displayed inequality that the paper later uses before orthonormalization.

## B. SDP subsection

### Label coverage

| Paper label | Kind | In blueprint? | Lean correspondence |
| --- | --- | --- | --- |
| `eq:primal-objective` | displayed equation | No | `sdpPrimalObjective` |
| `eq:dual-objective` | displayed equation | No | `sdpDualObjective` |
| `eq:dual-constraint` | displayed equation | No | `sdpDualSlackOperator` / feasibility |
| `lem:sdp` | lemma | Yes | `sdp` |
| `eq:slater` | displayed equation | No | `sdpComplementarySlacknessEquation` |
| `eq:primal-canonical` | displayed equation | No | no direct theorem; only matrix witness scaffold |
| `eq:dual-canonical` | displayed equation | No | no direct theorem; only matrix witness scaffold |
| `eq:dual-canonical-constraint` | displayed equation | No | no direct theorem; only matrix witness scaffold |
| `eq:complementary-slackness` | displayed equation | No | `MatrixSdpOptimalWitness.complementarySlackness` / `SdpOptimalPair.complementarySlackness` |

Exact overlap in this block: only `lem:sdp`.

### Exact missing statements

- `eq:primal-objective` (paper lines 69-74)
  ```tex
  \sup \quad \sum_g \,\Tr(T_g \cdot A_g)
  \qquad
  \text{s.t. } T_g \geq 0 \ \forall g,\ \sum_g T_g \leq I.
  ```

- `eq:dual-objective` and `eq:dual-constraint` (paper lines 75-79)
  ```tex
  \inf \quad \Tr(Z)
  \qquad
  \text{s.t. } Z \geq A_g.
  ```

- `eq:slater` (paper lines 84-87)
  ```tex
  T_g Z = T_g A_g,
  \qquad \forall g \in \polyfunc{m}{q}{d}.
  ```

- `eq:primal-canonical` (paper lines 97-101)
  ```tex
  \sup \quad \Tr(C^\dagger X)
  \qquad
  \text{s.t. } \Tr(D_{ij}^\dagger X) = b_{ij} \ \forall i,j,\ X \geq 0.
  ```

- `eq:dual-canonical` and `eq:dual-canonical-constraint` (paper lines 142-146)
  ```tex
  \inf \quad \sum_i\, z_{ij} b_{ij}
  \qquad
  \text{s.t. } \sum_{i,j} \,z_{ij} D_{ij} \geq C.
  ```

- `eq:complementary-slackness` (paper lines 177-180)
  ```tex
  X\Big( \sum_{i,j} \,z_{ij} D_{ij} - C \Big) \,=\, 0.
  ```

### Dependency chain and proof structure

Paper proof of `lem:sdp`:

1. Introduce `A_g = E_u A^u_{g(u)}`.
2. Rewrite the primal into canonical block SDP form.
3. Compute the canonical dual and identify it with `Z >= A_g`.
4. Use strict feasibility (Slater) for both primal and dual.
5. Invoke strong duality and complementary slackness.
6. Translate complementary slackness back to:
   - `sum_g T_g = I`
   - `T_g (Z - A_g) = 0`.

Lean correspondence:

- Direct operators:
  - `averagedPointOperator`
  - `sdpPrimalObjective`
  - `sdpDualObjective`
  - `sdpDualSlackOperator`
  - `sdpComplementarySlacknessEquation`
- The statement layer:
  - `SdpOptimalPair`
  - `SdpStatement`
- Matrix witness layer:
  - `MatrixSdpRealization`
  - `MatrixSdpOptimalWitness`

### Statement mismatches / compression notes

- Blueprint compression:
  - The blueprint keeps only the final SDP statement.
  - It omits all canonical-form labels and the explicit complementary-slackness label.
- Lean mismatch:
  - The paper primal constraint is `sum_g T_g <= I`.
  - `SdpOptimalPair` in Lean takes `T : Measurement`, so `sum_g T_g = I` is built into the object rather than derived at optimality.
  - The source comment in `Theorems.lean` explicitly acknowledges this mismatch and says a weaker `SubMeas` formulation will still be needed internally.

This is the cleanest formalization gap in the chapter: the theorem statement exists, but the proof really needs the missing weaker primal formulation and the canonical-SDP argument.

## C. Proof of the helper lemma

This is the largest gap. The blueprint keeps only one summary paragraph for the proof of `lem:self-improvement-helper`, while the paper has:

- two setup equations for the SDP witness,
- the full technical lemma `lem:add-in-u`,
- four separate proof branches,
- about thirty labeled intermediate equations.

### C1. Setup before `lem:add-in-u`

| Paper label | Kind | In blueprint? | Lean correspondence |
| --- | --- | --- | --- |
| `eq:Z-greater-than-A` | displayed equation | No | `dualDominatesAveragedPoint` |
| `eq:swap-Z-for-A` | displayed equation | No | `sdpComplementarySlacknessEquation` |
| `lem:add-in-u` | lemma | Yes | `addInU` |

Exact missing statements:

- `eq:Z-greater-than-A` (paper line 200)
  ```tex
  Z \geq (\E_{\bu} A^{\bu}_{g(\bu)}).
  ```

- `eq:swap-Z-for-A` (paper line 201)
  ```tex
  T_g \cdot Z = T_g \cdot (\E_{\bu} A^{\bu}_{g(\bu)}).
  ```

Lean mapping:

- `SelfImprovementHelperConclusion.dualDominatesAveragedPoint`
- `sdpComplementarySlacknessEquation`
- `sandwichedPolynomialOutcomeOperatorAt`
- `averagedSandwichedPolynomialSubMeas`

### C2. `lem:add-in-u`

#### Label coverage

| Paper label | Kind | In blueprint? | Lean correspondence |
| --- | --- | --- | --- |
| `eq:expand-that-H` | displayed equation | No | `averagedSandwichedPolynomialSubMeas` |
| `eq:move-one` | displayed equation | No | no dedicated theorem |
| `eq:move-one-cauchy-schwarz` | displayed equation | No | no dedicated theorem |
| `eq:move-another` | displayed equation | No | no dedicated theorem |
| `eq:move-another-cauchy-schwarz` | displayed equation | No | no dedicated theorem |
| `eq:change-one` | displayed equation | No | `AddInUStatement.transfer` conceptually |
| `eq:change-one-cauchy-schwarz` | displayed equation | No | no dedicated theorem |
| `eq:change-another` | displayed equation | No | `AddInUStatement.transfer` conceptually |

#### Exact missing statements

- `eq:expand-that-H` (paper lines 249-252)
  ```tex
  \E_{\bu} \sum_{(o, h) \in S_{\bu}} \bra{\psi} M^{\bu}_o \otimes H_h \ket{\psi}
  = \E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} M^{\bu}_o \otimes
      (A^{\bv}_{h(\bv)} \cdot T_h \cdot A^{\bv}_{h(\bv)}) \ket{\psi}.
  ```

- `eq:move-one` (paper lines 255-258)
  ```tex
  \eqref{eq:expand-that-H}
  \approx_{\sqrt{2\delta}}
  \E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bv}_{h(\bv)} \cdot M^{\bu}_o)
      \otimes (T_h \cdot A^{\bv}_{h(\bv)}) \ket{\psi}.
  ```

- `eq:move-one-cauchy-schwarz` (paper lines 261-265)
  ```tex
  \Big|\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bv}_{h(\bv)} \otimes I - I \otimes A^{\bv}_{h(\bv)})
      \cdot (M^{\bu}_o \otimes (T_h \cdot A^{\bv}_{h(\bv)}))\ket{\psi}\Big|
  ```
  ```tex
  \leq
  \sqrt{\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bv}_{h(\bv)} \otimes I - I \otimes A^{\bv}_{h(\bv)})
      \cdot (M^{\bu}_o \otimes T_h)
      \cdot (A^{\bv}_{h(\bv)} \otimes I - I \otimes A^{\bv}_{h(\bv)}) \ket{\psi}}
  ```
  ```tex
  \cdot \sqrt{\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi}  M^{\bu}_o \otimes
      (A^{\bv}_{h(\bv)} \cdot T_h\cdot  A^{\bv}_{h(\bv)}) \ket{\psi}}.
  ```

- `eq:move-another` (paper lines 279-282)
  ```tex
  \eqref{eq:move-one}
  \approx_{\sqrt{2\delta}}
  \E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bv}_{h(\bv)} \cdot M^{\bu}_o \cdot A^{\bv}_{h(\bv)})
      \otimes T_h  \ket{\psi}.
  ```

- `eq:move-another-cauchy-schwarz` (paper lines 285-288)
  ```tex
  \Big|\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} ((A^{\bv}_{h(\bv)} \cdot M^{\bu}_o) \otimes T_h)
      \cdot (A^{\bv}_{h(\bv)} \otimes I - I \otimes A^{\bv}_{h(\bv)})  \ket{\psi}\Big|
  ```
  ```tex
  \leq
  \sqrt{\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bv}_{h(\bv)} \cdot M^{\bu}_o \cdot A^{\bv}_{h(\bv)}) \otimes T_h  \ket{\psi}}
  ```
  ```tex
  \cdot \sqrt{\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bv}_{h(\bv)} \otimes I - I \otimes A^{\bv}_{h(\bv)})
      \cdot (M^{\bu}_o \otimes T_h)
      \cdot (A^{\bv}_{h(\bv)} \otimes I - I \otimes A^{\bv}_{h(\bv)}) \ket{\psi}}.
  ```

- `eq:change-one` (paper lines 300-303)
  ```tex
  \eqref{eq:move-another}
  \approx_{\sqrt{\zeta_{\mathrm{variance}}}}
  \E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bu}_{h(\bu)} \cdot M^{\bu}_o \cdot A^{\bv}_{h(\bv)})
      \otimes T_h  \ket{\psi}.
  ```

- `eq:change-one-cauchy-schwarz` (paper lines 306-310)
  ```tex
  \Big|\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} ((A^{\bv}_{h(\bv)} - A^{\bu}_{h(\bu)}) \cdot M^{\bu}_o \cdot A^{\bv}_{h(\bv)})
      \otimes T_h  \ket{\psi}\Big|
  ```
  ```tex
  \leq
  \sqrt{\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} ((A^{\bv}_{h(\bv)} - A^{\bu}_{h(\bu)}) \cdot M^{\bu}_o
      \cdot (A^{\bv}_{h(\bv)} - A^{\bu}_{h(\bu)})) \otimes T_h  \ket{\psi}}
  ```
  ```tex
  \cdot \sqrt{\E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bv}_{h(\bv)} \cdot M^{\bu}_o \cdot A^{\bv}_{h(\bv)}) \otimes T_h  \ket{\psi}}.
  ```

- `eq:change-another` (paper lines 320-323)
  ```tex
  \eqref{eq:change-one}
  \approx_{\sqrt{\zeta_{\mathrm{variance}}}}
  \E_{\bu, \bv} \sum_{(o, h) \in S_{\bu}}
    \bra{\psi} (A^{\bu}_{h(\bu)} \cdot M^{\bu}_o \cdot A^{\bu}_{h(\bu)})
      \otimes T_h  \ket{\psi}.
  ```

#### Dependency chain and proof structure

The proof of `lem:add-in-u` has a very rigid four-step structure:

1. Expand averaged `H_h` by a fresh point `v`.
2. Move the first `A^v_{h(v)}` from Bob to Alice via self-consistency of `A`.
3. Move the second `A^v_{h(v)}` the same way.
4. Replace `v` by `u` twice using `lem:global-variance-of-points`.

The blueprint keeps only one paragraph for this entire chain.

Lean gap:

- `AddInUStatement.transfer` captures only the end result.
- There are no named intermediate Lean lemmas corresponding to the four labeled paper moves.
- The theorem `addInU` is still a `sorry`.

### C3. Completeness branch

#### Label coverage

| Paper label | Kind | In blueprint? | Lean correspondence |
| --- | --- | --- | --- |
| `eq:bracketize-the-expression` | displayed equation | No | helper completeness proof only |
| `eq:yet-another-move-a` | displayed equation | No | no dedicated theorem |
| `eq:mysterious-case-of-the-disappearing-a` | displayed equation | No | uses projectivity of `A` |
| `eq:gonna-use-this-later-H-versus-Z` | displayed equation | No | `helperResidualBound` / `bounded` are downstream packaged consequences |

#### Exact missing statements

- `eq:bracketize-the-expression` (paper lines 353-357)
  ```tex
  \sum_h \bra{\psi} H_h \otimes I \ket{\psi}
  = \E_{\bu} \sum_a \bra{\psi}
      (A^{\bu}_{a} \cdot T_{[h(\bu) = a]} \cdot A^{\bu}_{a}) \otimes I
    \ket{\psi}.
  ```

- `eq:yet-another-move-a` (paper lines 360-363)
  ```tex
  \eqref{eq:bracketize-the-expression}
  \approx_{2\sqrt{\delta}}
  \E_{\bu} \sum_a \bra{\psi}
    ( T_{[h(\bu)=a]} \cdot A^{\bu}_{a}) \otimes A^{\bu}_{a} \ket{\psi}.
  ```

- `eq:mysterious-case-of-the-disappearing-a` (paper lines 376-379)
  ```tex
  \eqref{eq:yet-another-move-a}
  \approx_{\sqrt{\delta}}
  \E_{\bu} \sum_a \bra{\psi}
    ( T_{[h(\bu)=a]} \cdot A^{\bu}_{a}) \otimes I \ket{\psi}.
  ```

- `eq:gonna-use-this-later-H-versus-Z` (paper lines 403-404)
  ```tex
  \sum_h \bra{\psi} H_h \otimes I \ket{\psi}
  \geq \bra{\psi}  Z \otimes I \ket{\psi} - 3\sqrt{\delta}.
  ```

### C4. Consistency-with-`A` branch

#### Label coverage

| Paper label | Kind | In blueprint? | Lean correspondence |
| --- | --- | --- | --- |
| `eq:consistency-with-A-baby-step` | displayed equation | No | `pointConsistency` packages its final result |
| `eq:explicit-bound-for-A-consistency` | displayed equation | No | `pointConsistency` / later reused in self-consistency and boundedness branches |

#### Exact missing statements

- `eq:consistency-with-A-baby-step` (paper lines 421-423)
  ```tex
  \E_{\bu \sim \F_q^m} \sum_{a \neq b}
    \bra{\psi} A^{\bu}_a \otimes H_{[h(\bu) = b]} \ket{\psi}
  = \E_{\bu \sim \F_q^m} \sum_{a, h: h(\bu) \neq a}
    \bra{\psi} A^{\bu}_a \otimes H_h \ket{\psi}.
  ```

- `eq:explicit-bound-for-A-consistency` (paper lines 435-436)
  ```tex
  \E_{\bu \sim \F_q^m} \sum_{a \neq b}
    \bra{\psi} A^{\bu}_a \otimes H_{[h(\bu) = b]} \ket{\psi}
  \leq 4 \sqrt{\zeta_{\mathrm{variance}}}.
  ```

### C5. Strong self-consistency branch

#### Label coverage

| Paper label | Kind | In blueprint? | Lean correspondence |
| --- | --- | --- | --- |
| `eq:h-sandwich` | displayed equation | No | `sandwichedPolynomialOutcomeOperatorAt` |
| `eq:h-blt` | displayed equation | No | same definition + projectivity |
| `eq:self-consistency-baby-step` | displayed equation | No | `strongSelfConsistency` packages final conclusion |
| `eq:release-the-kraken` | displayed equation | No | `lem:add-in-u` specialized with `M = H` |
| `eq:threw-in-h-prime` | displayed equation | No | no dedicated theorem |
| `eq:added-indicator` | displayed equation | No | no dedicated theorem |
| `eq:swapped-u-for-v` | displayed equation | No | no dedicated theorem |
| `eq:swapped-u-for-cauchy-schwarz` | displayed equation | No | no dedicated theorem |
| `eq:swapped-u-for-v-this-time-it's-personal` | displayed equation | No | Schwartz-Zippel step |
| `eq:gonna-use-this-later` | displayed equation | No | local auxiliary estimate only |
| `eq:delete-an-A` | displayed equation | No | no dedicated theorem |
| `eq:swap-u-for-v-attack-of-the-clones` | displayed equation | No | no dedicated theorem |
| `eq:move-over-v` | displayed equation | No | no dedicated theorem |

#### Exact missing statements

- `eq:h-sandwich` (paper line 451)
  ```tex
  H^u_h = A^u_{h(u)} \cdot T_h \cdot A^u_{h(u)}
       = A^u_{h(u)} \cdot H^u_h \cdot A^u_{h(u)}.
  ```

- `eq:h-blt` (paper line 452)
  ```tex
  A^u_{h(u)} \cdot H^u_{h'} \cdot A^u_{h(u)}
  =  H^u_{h'} \cdot A^u_{h(u)}
  = (A^u_{h(u)} \cdot T_{h'} \cdot A^u_{h(u)}) \cdot \bone[h(u) = h'(u)].
  ```

- `eq:self-consistency-baby-step` (paper lines 455-457)
  ```tex
  \sum_{h\in\polyfunc{m}{q}{d}} \bra{\psi} H_h \otimes H_h \ket{\psi}
  = \E_{\bu \sim \F_q^m} \sum_{h \in \polyfunc{m}{q}{d}}
      \bra{\psi} H_h^{\bu} \otimes H_h \ket{\psi}.
  ```

- `eq:release-the-kraken` (paper lines 465-468)
  ```tex
  \eqref{eq:self-consistency-baby-step}
  \approx_{4 \sqrt{\zeta_{\mathrm{variance}}}}
  \E_{\bu \sim \F_q^m} \sum_{h \in \polyfunc{m}{q}{d}}
    \bra{\psi} (A^{\bu}_{h(\bu)} \cdot H_h^{\bu} \cdot A^{\bu}_{h(\bu)})
      \otimes T_h \ket{\psi}.
  ```

- `eq:threw-in-h-prime` (paper lines 471-474)
  ```tex
  \eqref{eq:release-the-kraken}
  \approx_{2\sqrt{\zeta_{\mathrm{variance}}} + \frac{md}{q}}
  \E_{\bu \sim \F_q^m} \sum_{h, h' \in \polyfunc{m}{q}{d}}
    \bra{\psi} (A^{\bu}_{h(\bu)} \cdot H^{\bu}_{h'} \cdot A^{\bu}_{h(\bu)})
      \otimes T_h \ket{\psi}.
  ```

- `eq:added-indicator` (paper lines 478-480)
  ```tex
  \eqref{eq:threw-in-h-prime}-\eqref{eq:release-the-kraken}
  = \E_{\bu \sim \F_q^m} \sum_{h \neq h'}
      \bra{\psi}  (A^{\bu}_{h(\bu)} \cdot T_{h'} \cdot A^{\bu}_{h(\bu)})
        \otimes T_h \ket{\psi} \cdot \bone[h(\bu) = h'(\bu)].
  ```

- `eq:swapped-u-for-v` (paper lines 484-487)
  ```tex
  \eqref{eq:added-indicator}
  \approx_{\sqrt{\zeta_{\mathrm{variance}}}}
  \E_{\bu,\bv} \sum_{h \neq h'}
    \bra{\psi}  (A^{\bv}_{h(\bv)} \cdot T_{h'} \cdot A^{\bu}_{h(\bu)})
      \otimes T_h \ket{\psi} \cdot \bone[h(\bu) = h'(\bu)].
  ```

- `eq:swapped-u-for-cauchy-schwarz` (paper lines 490-494)
  ```tex
  \Big|\E_{\bu,\bv} \sum_{h \neq h'}
    \bra{\psi} ( (A^{\bu}_{h(\bu)} - A^{\bv}_{h(\bv)}) \cdot T_{h'}
      \cdot A^{\bu}_{h(\bu)}) \otimes T_h \ket{\psi}
      \cdot \bone[h(\bu) = h'(\bu)]\Big|
  ```
  ```tex
  \leq
  \sqrt{\E_{\bu,\bv} \sum_{h \neq h'}
    \bra{\psi}  ( (A^{\bu}_{h(\bu)} - A^{\bv}_{h(\bv)}) \cdot T_{h'}
      \cdot (A^{\bu}_{h(\bu)} - A^{\bv}_{h(\bv)})) \otimes T_h\ket{\psi}} 
  ```
  ```tex
  \cdot \sqrt{\E_{\bu,\bv} \sum_{h \neq h'}
    \bra{\psi} (A^{\bu}_{h(\bu)} \cdot T_{h'} \cdot A^{\bu}_{h(\bu)})
      \otimes T_h\ket{\psi} \cdot \bone[h(\bu) = h'(\bu)]}.
  ```

- `eq:swapped-u-for-v-this-time-it's-personal` (paper lines 508-511)
  ```tex
  \eqref{eq:swapped-u-for-v}
  \approx_{\sqrt{\zeta_{\mathrm{variance}}}}
  \E_{\bu,\bv} \sum_{h \neq h'}
    \bra{\psi}  (A^{\bv}_{h(\bv)} \cdot T_{h'} \cdot A^{\bv}_{h(\bv)})
      \otimes T_h \ket{\psi} \cdot \bone[h(\bu) = h'(\bu)].
  ```

- `eq:gonna-use-this-later` (paper lines 521-526)
  ```tex
  \E_{\bu,\bv} \sum_{h \neq h'}
    \bra{\psi}  (A^{\bv}_{h(\bv)} \cdot T_{h'} \cdot A^{\bv}_{h(\bv)})\otimes T_h\ket{\psi}
  \leq 1.
  ```

- `eq:delete-an-A` (paper lines 538-540)
  ```tex
  \E_{\bu \sim \F_q^m} \sum_{h, h' \in \polyfunc{m}{q}{d}}
    \bra{\psi} (H^{\bu}_{h'} \cdot A^{\bu}_{h(\bu)}) \otimes T_h \ket{\psi}.
  ```

- `eq:swap-u-for-v-attack-of-the-clones` (paper lines 543-546)
  ```tex
  \eqref{eq:delete-an-A}
  \approx_{\sqrt{\zeta_{\mathrm{variance}}}}
  \E_{\bu, \bv} \sum_{h, h' \in \polyfunc{m}{q}{d}}
    \bra{\psi} (H^{\bu}_{h'} \cdot A^{\bv}_{h(\bv)}) \otimes T_h \ket{\psi}.
  ```

- `eq:move-over-v` (paper lines 564-567)
  ```tex
  \eqref{eq:swap-u-for-v-attack-of-the-clones}
  \approx_{\sqrt{2\delta}}
  \E_{\bu, \bv} \sum_{h, h' \in \polyfunc{m}{q}{d}}
    \bra{\psi} H^{\bu}_{h'}  \otimes (T_h \cdot A^{\bv}_{h(\bv)}) \ket{\psi}.
  ```

#### Dependency chain and proof structure

This branch uses:

1. the specialization of `lem:add-in-u` with `M = H`,
2. the pointwise identities `eq:h-sandwich` and `eq:h-blt`,
3. two global-variance substitutions,
4. a Schwartz-Zippel bound on `Pr_u[h(u) = h'(u)]`,
5. the previously proved `A`-consistency estimate `eq:explicit-bound-for-A-consistency`.

This is the densest subproof in the chapter and is almost entirely absent from the blueprint.

### C6. Boundedness branch

There is no new label on the opening displayed expression in this branch, but its proof depends directly on:

- `eq:explicit-bound-for-A-consistency`
- `eq:gonna-use-this-later-H-versus-Z`

So the blueprint's one-sentence boundedness summary is relying on two labeled helper facts that are no longer blueprint-addressable.

## D. Projective self-improvement subsection

### Label coverage

| Paper label | Kind | In blueprint? | Lean correspondence |
| --- | --- | --- | --- |
| `sec:self-improvement-projective` | subsection label | No | none |
| `thm:self-improvement` | theorem | Yes | `selfImprovement` |
| `item:self-improvement-projective-G-consistency` | item | No | hypothesis `hcons` of `selfImprovement` |
| `item:self-improvement-projective-completeness` | item | No | `SelfImprovementConclusion.completeness` |
| `item:self-improvement-projective-A-consistency` | item | No | `SelfImprovementConclusion.pointConsistency` |
| `item:self-improvement-projective-self` | item | No | `SelfImprovementConclusion.selfCloseness` |
| `item:self-improvement-projective-boundedness` | item | No | `projectiveResidualBound`, `bounded`, `dualDominatesAveragedPoint` |
| `eq:approx-between-H-with-and-without-hat` | displayed equation | No | `SelfImprovementConclusion.witness` stores the orthonormalization relation |
| `eq:approx-data-processed` | displayed equation | No | `SelfImprovementConclusion.witness` stores the postprocessed relation |
| `eq:almost-there-self-improvement-edition` | displayed equation | No | `projectiveResidualOperator`, `projectiveBoundednessGap` |

Exact overlap in this block: only `thm:self-improvement`.

### Exact missing statements

- `sec:self-improvement-projective`
  - No mathematical statement; this is the subsection anchor for the orthonormalization/projective transfer stage.

- `item:self-improvement-projective-G-consistency` (paper lines 639-642)
  ```tex
  \text{On average over } \bu \sim \F_q^{m}, \qquad
  A^{u}_a \otimes I \simeq_{\nu} I \otimes G_{[g(u)=a]}.
  ```

- `item:self-improvement-projective-completeness` (paper lines 650-653)
  ```tex
  \text{If } H = \sum_h H_h, \text{ then } \qquad
  \bra{\psi} H \otimes I \ket{\psi} \geq (1-\nu)-\zeta.
  ```

- `item:self-improvement-projective-A-consistency` (paper lines 654-657)
  ```tex
  \text{On average over } \bu \sim \F_q^m, \qquad
  A^u_a \otimes I \simeq_{\zeta} I \otimes H_{[h(u) = a]}.
  ```

- `item:self-improvement-projective-self` (paper lines 658-660)
  ```tex
  H_h \otimes I \approx_{\zeta} I \otimes H_h.
  ```

- `item:self-improvement-projective-boundedness` (paper lines 662-669)
  ```tex
  \bra{\psi} Z \otimes (I - H) \ket{\psi} \leq \zeta
  ```
  and, for each `h in polyfunc`,
  ```tex
  Z \geq \left(\E_{\bu} A^{\bu}_{h(\bu)}\right).
  ```

- `eq:approx-between-H-with-and-without-hat` (paper lines 692-693)
  ```tex
  \widehat{H}_h \otimes I \approx_{\widehat{\zeta}_{\mathrm{ortho}}} H_{h} \otimes I.
  ```

- `eq:approx-data-processed` (paper lines 700-701)
  ```tex
  \widehat{H}_{[h(u)=a]} \otimes I
  \approx_{\widehat{\zeta}_{\mathrm{dataprocess}}}
  H_{[h(u)=a]} \otimes I.
  ```

- `eq:almost-there-self-improvement-edition` (paper line 749)
  ```tex
  \bra{\psi} Z \otimes I \ket{\psi}
    -\E_{\bu} \sum_a \bra{\psi}  A^{\bu}_{a} \otimes H_{[h(\bu)=a]} \ket{\psi}.
  ```

### Dependency chain and proof structure

Paper:

1. Apply `lem:self-improvement-helper` to obtain non-projective `\widehat H`.
2. Apply `thm:orthonormalization` to get projective `H`.
3. Use `prop:self-consistency-implies-data-processing` to transfer evaluation families.
4. Transfer the four helper conclusions one by one:
   - completeness via `prop:completeness-transfer-self-consistent-A`,
   - consistency via `prop:triangle-sub`,
   - self-consistency via `prop:two-notions-of-self-consistency` plus triangle,
   - boundedness via the helper boundedness inequality plus postprocessed closeness.

Lean:

- `SelfImprovementConclusion.witness` already stores:
  - the helper witness,
  - the orthonormalization closeness relation,
  - the postprocessed evaluation-family closeness relation.
- `selfImprovement` packages exactly this architecture, but remains `sorry`.
- `selfImprovementFromSubMeas` is already implemented as the bridge from measurement input to the submeasurement-input form used elsewhere.

### Statement mismatches / compression notes

- Blueprint compression:
  - The blueprint theorem statement keeps the right mathematics, but again drops all item labels and both intermediate projective-transfer equations.
  - The proof paragraph compresses the entire orthonormalization/data-processing transfer into one prose paragraph.

## Cross-cutting mismatches and formalization blockers

### 1. Label loss is the dominant blueprint gap

The paper uses labeled sub-items and labeled intermediate equations as reusable proof waypoints. The blueprint removes almost all of them.

Practical consequence:

- Many later references in the paper are to theorem items, not just whole lemmas.
- The self-improvement chapter is especially dependent on these local references because the helper proof branches into four quantitatively different arguments.

### 2. The Lean scaffold is broader than the blueprint, but narrower than the paper proof

The Lean files already formalize more than the blueprint exposes:

- helper/projective boundedness operators,
- averaged sandwiched constructions,
- matrix witness records,
- witness packaging for orthonormalization and data processing.

But Lean still does not expose the paper's internal proof-step lemmas as named results. The gap is:

- paper: rich internal proof graph,
- blueprint: only top-level prose summary,
- Lean: top-level theorem interfaces, but no proved internal graph yet.

### 3. Important Lean statement mismatch: `addInU` does not assume optimality of `T`

Paper and blueprint:

- `lem:add-in-u` assumes `T = {T_h}` is an optimal solution of the primal SDP.

Lean:

- `lemma addInU ... (T : Measurement ...) ... : AddInUStatement ...`
  has no explicit optimality assumption.
- Instead, `AddInUStatement` contains a `varianceBound` field asserting the needed global-variance control on `T.toSubMeas`.

Interpretation:

- Lean is currently packaging the needed downstream consequence of optimality rather than the optimality hypothesis itself.
- That is workable, but it is not statement-faithful to either the paper or the blueprint.

### 4. Important Lean statement mismatch: the SDP primal is already a measurement

Paper:

- primal variables satisfy `sum_g T_g <= I`.
- equality `sum_g T_g = I` is derived from the Slater/complementary-slackness argument.

Lean:

- `SdpOptimalPair` takes `T : Measurement`, so equality is built in.

Interpretation:

- This is fine as an output package.
- It is not faithful as the raw SDP statement, so the proof will still need an internal weaker formulation or an auxiliary construction.

### 5. Paper-side citation typos worth noting

In the projective theorem proof, the paper appears to cite helper conclusions using the projective item labels:

- line 717 cites `item:self-improvement-projective-completeness` of `lem:self-improvement-helper`
- line 721 cites `item:self-improvement-projective-A-consistency` of `lem:self-improvement-helper`
- line 747 cites `item:self-improvement-projective-boundedness` of `lem:self-improvement-helper`

These should presumably refer to the non-projective helper item labels instead:

- `item:self-improvement-completeness`
- `item:self-improvement-A-consistency`
- `item:self-improvement-boundedness`

This is a paper issue, not a blueprint issue, but it is useful to know before trying to preserve labels exactly.

## Suggested proof-order for Lean

If the goal is a faithful Lean formalization with a useful blueprint, the natural order is:

1. Make the SDP layer faithful.
   - Introduce or internalize a `SubMeas`-valued primal formulation.
   - Prove canonical duality, Slater, and complementary slackness.
2. Prove `lem:add-in-u` as a standalone technical transfer theorem.
   - Strong candidate for several internal helper lemmas mirroring:
     - move first `A`,
     - move second `A`,
     - replace `v` by `u` on the left,
     - replace `v` by `u` on the right.
3. Prove `lem:self-improvement-helper`.
   - Keep the four proof branches explicit.
4. Prove `thm:self-improvement`.
   - Use the already-packaged witness structure for orthonormalization and data processing.
5. Optionally expose a few internal helper lemmas in the blueprint.
   - At minimum, restore labels for:
     - theorem items,
     - SDP primal/dual equations,
     - `eq:Z-greater-than-A`,
     - `eq:swap-Z-for-A`,
     - the major `lem:add-in-u` transitions,
     - `eq:explicit-bound-for-A-consistency`,
     - `eq:gonna-use-this-later-H-versus-Z`,
     - `eq:approx-between-H-with-and-without-hat`,
     - `eq:approx-data-processed`.

## Bottom line

The chapter gap is real and structural, not just quantitative:

- Paper: 56 labels and a highly articulated proof graph.
- Blueprint: 5 labels and compressed prose proofs.
- Lean: good theorem packaging and definitions, but the four core proofs are still placeholders.

The main missing content is not new theorem statements; it is the internal dependency graph that makes the chapter formalizable:

- SDP canonicalization and complementary slackness,
- the four-move `add-in-u` transfer argument,
- the explicit branch structure of the helper proof,
- the orthonormalization/data-processing bridge to the projective theorem.
