---
title: Quaternionic Elliptic Coefficients as Lattice Sums
description: Eisenstein sums and coefficient identities, separated from open research directions.
section: Quaternionic analysis
article-kind: exposition
order: 3
---
# Quaternionic Elliptic Coefficients as Lattice Sums \label{0060}

:::discussion
The elliptic construction starts from an arbitrary full-rank lattice. Its coefficients supply a first connection to lattice Eisenstein sums. The precise statements below lead to representations and special values, followed by questions about arithmetic multiplication and periods.
:::

## Higher derivatives and Eisenstein sums

\label{0061}

For $\nu=(n_1,n_2,n_3)\in\mathbb N_0^3$, set
$$
|\nu|=n_1+n_2+n_3,\quad
\partial^\nu=\partial_{x_1}^{n_1}\partial_{x_2}^{n_2}\partial_{x_3}^{n_3},
\quad G_\nu=\partial^\nu G.
$$
Write $\epsilon_j$ for the multi-index with a single $1$ in position $j$, for $j\in\{1,2,3\}$.

::::construction \label{0062} | Higher Eisenstein and elliptic sums
Version: 1
Uses: \autoref{0061}, [lattice setup](\ref{0068}).
Justification: Absolute convergence and periodicity in \autoref{0063}.
Origin: consequence
---
Let $L\subset\mathbb H$ be a full-rank lattice and let $\nu\in\mathbb N_0^3$ satisfy $|\nu|\ge2$. Form
$$
E_\nu(L)=\sum_{\lambda\in L^*}G_\nu(\lambda),
\qquad
\wp_{L,\nu}(q)=\sum_{\lambda\in L}G_\nu(q+\lambda)-E_\nu(L)
\quad(q\notin L).
$$
::::

::::proposition \label{0063} | Convergence and periodicity of the higher sums
Version: 1
Uses: \autoref{0062}, \autoref{006S}, the lattice-count estimate in \autoref{006B}.
Review: pending
Formal: verified
Formal-evidence: [Lean checking record](../evidence/lean-N1-v2.html#MathResearch.Fueter.N2_v1)
Origin: consequence
---
For every full-rank lattice $L\subset\mathbb H$ and every $\nu\in\mathbb N_0^3$ with $|\nu|\ge2$, the Eisenstein series in \autoref{0062} converges absolutely. The defining series for $\wp_{L,\nu}$ converges absolutely and locally uniformly on $\mathbb H\setminus L$. For every $\omega\in L$ and $q\notin L$,
$$
\wp_{L,\nu}(q+\omega)=\wp_{L,\nu}(q).
$$

:::proof Proof of \ref{0063}
\autoref{006S} gives decay $|q|^{-3-|\nu|}$, with exponent at least $5$. The lattice-count estimate from the proof of \autoref{006B} therefore proves absolute convergence, uniformly on compact sets away from the lattice for the translated sum. Absolute convergence permits reindexing $\lambda\mapsto\lambda+\omega$, which proves periodicity.
:::
::::

::::proposition \label{0064} | Coefficients at the singularity
Version: 2
Uses: \autoref{0061}, \autoref{0062}, \autoref{0063}, \autoref{006B}.
Review: pending
Formal: verified
Formal-evidence: [Lean checking record](../evidence/lean-N1-v2.html#MathResearch.Fueter.N1_v2)
Origin: consequence
---
Let $L\subset\mathbb H$ be a full-rank lattice and $j\in\{1,2,3\}$. Let $h_j$ be the smooth extension near $0$ of $\wp_{L,j}-G_j$ supplied by \autoref{006B}. For every $\mu\in\mathbb N_0^3$ with $|\mu|\ge1$,
$$
\partial^\mu h_j(0)=E_{\mu+\epsilon_j}(L).
$$

:::proof Proof of \ref{0064}
Differentiate the convergent series for $h_j$ from \autoref{006B} and evaluate at $q=0$. The subtracted constants disappear, leaving $\sum_{\lambda\in L^*}G_{\mu+\epsilon_j}(\lambda)$. This converges absolutely since $|\mu+\epsilon_j|\ge2$.
:::
::::

::::corollary \label{0065} | Parity cancellation
Version: 1
Uses: \autoref{0062}, \autoref{0063}, \autoref{006S}.
Review: pending
Formal: verified
Formal-evidence: [Lean checking record](../evidence/lean-N1-v2.html#MathResearch.Fueter.N3_v1)
Origin: derivation
---
For every full-rank lattice $L\subset\mathbb H$ and every $\nu\in\mathbb N_0^3$ with even $|\nu|\ge2$,
$$
E_\nu(L)=0.
$$

:::proof Proof of \ref{0065}
By \autoref{006S}, $G_\nu$ is odd when $|\nu|$ is even. The terms at $\lambda$ and $-\lambda$ cancel, and absolute convergence from \autoref{0063} justifies pairing them.
:::
::::

:::discussion
These are foundational identities, with no novelty claim. They explain how higher Eisenstein sums enter the regular part of the elliptic construction. Among the absolutely convergent sums, order $2$ vanishes by \autoref{0065}, so order $3$ is the first order not eliminated by this parity argument. For related lattice sums and Laurent coefficients, see [[1]](#ref-krausshar-2001), §§4–5.
:::

The full-lattice Eisenstein sum in \autoref{0062} is twice the positive-semilattice sum of [[1, §4, eq. (8), p. 1018]](#ref-krausshar-2001) at odd derivative order. The regularized first-derivative sum is [[1, §4, eq. (12), p. 1019]](#ref-krausshar-2001). \autoref{0064} uses real Taylor derivatives; the source’s expansion [[1, eq. (13), p. 1020]](#ref-krausshar-2001) uses Fueter polynomials.

## Eisenstein representations

:::discussion
Varying the lattice produces [Eisenstein functions on SL₄](lattice-eisenstein-series.md). Their irreducible module, inducing parameter, and compact types are established there with proofs. This lattice action differs from the Möbius action on regular functions in [the discrete-series](fueter-discrete-series.md) and [Hardy](fueter-hardy-space.md) constructions.
:::

## Harmonic theta series

:::discussion
The kernel derivatives have [harmonic polynomial numerators](\ref{009B}). Their convergent lattice sums admit a [Mellin formula](\ref{00A0}); even integral lattices give [harmonic theta cusp forms](\ref{008D}) and [critical L-values](\ref{00A1}). The [cubic example](\ref{00A4}) identifies a specific coefficient with the value at five of the weight-six newform η(2τ)¹².

The order-one sum and its proposed connection to quasi-periods still need a regularization theorem. Other arithmetic lattices, Hecke decompositions, and algebraic period normalizations remain open directions.
:::

\label{0066}

## Open Directions

### Multiplication and Arithmetic Lattices

Lattices with an action by elements of a quaternion algebra suggest transformation laws for the elliptic functions and quasi-periods. The action and its hypotheses need precise statements. A transformation identity and an independent arithmetic constraint are different conclusions.

### Period Relations

The additivity of $\eta_L$ is part of \autoref{006F}. Relating it to a residue or to integrals on $\mathbb H/L$ requires further statements fixing normalization, orientation, and left/right regularity. The [closed pairings and pullback identities](regular-differential-forms.md) supply local results; quotient cohomology remains open.

The [literature guide](literature.md) collects sources and further reading. These questions remain in the research notebook for investigation.

## References

1. <span id="ref-krausshar-2001"></span> R. S. Kraußhar, [*On a New Type of Eisenstein Series in Clifford Analysis*](https://doi.org/10.4171/ZAA/1057), Zeitschrift für Analysis und ihre Anwendungen **20** (2001), no. 4, 1007–1029. [Open text](https://ems.press/content/serial-article-files/35214).
