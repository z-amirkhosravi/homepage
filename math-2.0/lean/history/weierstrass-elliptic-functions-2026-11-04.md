---
title: Quaternionic Weierstrass Functions and Quasi-Periods
description: Precise lattice constructions, propositions, and corollaries with separately attached proofs.
section: Quaternionic analysis
article-kind: exposition
order: 2
---
# Quaternionic Weierstrass Functions and Quasi-Periods \label{0067}

:::discussion
Summing translates of derivatives of the Cauchy–Fueter kernel produces quaternionic analogues of Weierstrass functions. This article develops three periodic functions and a zeta function with additive quasi-periods. Prerequisites are [the kernel and Fueter regularity](foundations.md), Taylor's theorem, and uniform convergence of differentiated series.
:::

## 1. The lattice

\label{0068}

Fix a full-rank lattice $L\subset\mathbb H$, written as
$$
L=\mathbb Z\omega_0+\mathbb Z\omega_1+\mathbb Z\omega_2+\mathbb Z\omega_3,
$$
where the four generators are linearly independent over $\mathbb R$.

\label{0069}
Put $L^*=L\setminus\{0\}$.

Use the fixed coordinates $q=t+\sum_{j=1}^3e_jx_j$ and the functions
$$
G(q)=\frac{\bar q}{|q|^4},\qquad G_j=\partial_{x_j}G,\quad j=1,2,3.
$$
Each bracket in the following lattice sums is a single summand; convergence is asserted for the bracketed sums.

:::discussion
The naive sum of translates of $G_j$ has borderline decay $|\lambda|^{-4}$ in four dimensions. Subtracting the constant $G_j(\lambda)$ gains an extra power of decay. The individual terms inside a bracket must not be split into divergent lattice sums.
:::

## 2. The elliptic functions

::::construction \label{006A} | Regularized first-derivative lattice sums
Version: 1
Uses: [lattice setup](\ref{0068}).
Justification: Convergence and regularity in \autoref{006B}; periodicity in \autoref{006C}.
Origin: literature
Cite: [[2, §4, eq. (12), p. 1019]](#ref-krausshar-2001)
---
For a full-rank lattice $L\subset\mathbb H$, $j\in\{1,2,3\}$, and $q\in\mathbb H\setminus L$, form the series
$$
\wp_{L,j}(q)=G_j(q)+
\sum_{\lambda\in L^*}
\bigl[G_j(q+\lambda)-G_j(\lambda)\bigr].
$$
::::

:::discussion
Here “elliptic” means lattice-periodic and Fueter-regular away from isolated singularities. \autoref{006B} and \autoref{006C} supply these properties for \autoref{006A}.
:::

::::proposition \label{006B} | Convergence and regularity
Version: 2
Uses: \autoref{006A}, \autoref{006R}, \autoref{006S}.
Review: pending
Formal: verified
Formal-evidence: [Lean checking record](../evidence/lean-N1-v2.html#MathResearch.Fueter.E1_v2)
Origin: consequence
---
Let $L\subset\mathbb H$ be a full-rank lattice and $j\in\{1,2,3\}$. The series in \autoref{006A} converges absolutely and uniformly on every compact subset of $\mathbb H\setminus L$. It may be differentiated term by term to every real order, with locally uniform convergence of the differentiated series. Its sum is both left and right Fueter-regular.

For every $\omega\in L$, the function
$$
q\longmapsto\wp_{L,j}(q)-G_j(q-\omega)
$$
extends to a smooth, left and right regular function on a neighborhood of $\omega$.

:::proof Proof of \ref{006B}
For a compact set $K\subset\mathbb H\setminus L$, choose $R$ with $|q|\le R$ on $K$. If $|\lambda|>2R$, the segment from $\lambda$ to $\lambda+q$ stays at distance at least $|\lambda|/2$ from $0$. The derivative bound from the foundations page and the mean-value estimate give
$$
|G_j(\lambda+q)-G_j(\lambda)|
\le C R|\lambda|^{-5}.
$$
A full-rank lattice has $O(r^4)$ points in a ball of radius $r$: write $L=A\mathbb Z^4$ for an invertible real matrix $A$ and use equivalence of norms. Summing over dyadic shells now shows $\sum_{\lambda\in L^*}|\lambda|^{-p}<\infty$ for $p>4$. This proves absolute, locally uniform convergence.

After $m\ge1$ real derivatives, the constant subtraction vanishes and each tail term is bounded by $C_{K,m}|\lambda|^{-4-m}$. All differentiated series therefore converge locally uniformly. The finitely many terms omitted from these tail estimates are smooth away from their singularities. The standard theorem on locally uniform convergence of derivatives permits differentiation of the sum.

Every summand is left and right regular by \autoref{006R}, including the subtracted constant. Termwise differentiation proves regularity of the sum. In a small ball around any lattice point, remove its one singular summand; the remaining series and its derivatives converge uniformly and are regular there.
:::
::::

::::proposition \label{006C} | Parity and periodicity
Version: 2
Uses: \autoref{006A}, \autoref{006B}, \autoref{006S}.
Review: pending
Formal: verified
Formal-evidence: [Lean checking record](../evidence/lean-N1-v2.html#MathResearch.Fueter.E2_v2)
Origin: consequence
---
Let $L\subset\mathbb H$ be a full-rank lattice and $j\in\{1,2,3\}$. For all $q\in\mathbb H\setminus L$ and $\omega\in L$,
$$
\wp_{L,j}(-q)=\wp_{L,j}(q),\qquad
\wp_{L,j}(q+\omega)=\wp_{L,j}(q).
$$

:::proof Proof of \ref{006C}
Every first real partial derivative of $\wp_{L,j}$ is the absolutely convergent sum
$$
\partial_{x_\mu}\wp_{L,j}(q)
=\sum_{\lambda\in L}\partial_{x_\mu}G_j(q+\lambda),
\qquad \mu=0,1,2,3,\quad x_0=t.
$$
Reindexing this convergent sum shows that the derivatives are $L$-periodic. Hence
$$
H_\omega(q)=\wp_{L,j}(q+\omega)-\wp_{L,j}(q)
$$
has zero real gradient. The complement of a discrete lattice in $\mathbb R^4$ is path connected, so $H_\omega$ is a constant $c_\omega$.

Since $G_j$ is even, reindexing the absolutely convergent defining series by $\lambda\mapsto-\lambda$ shows that $\wp_{L,j}$ is even. Consequently
$$
H_\omega(-q-\omega)
=\wp_{L,j}(-q)-\wp_{L,j}(-q-\omega)
=-H_\omega(q).
$$
Both sides are constant in $q$, so $c_\omega=-c_\omega$, and therefore $c_\omega=0$.
:::
::::

:::discussion
The proof reindexes the absolutely convergent derivative series, then uses evenness to remove the possible constant increment. It does not reindex an unregularized borderline sum.
:::

## 3. The zeta function

For the classical zeta function and its derivative and quasi-period identities, see [[3, §2.1, p. 57]](#ref-krausshar-2004).

::::construction \label{006D} | Subtraction of the first Taylor polynomial
Version: 1
Uses: [lattice setup](\ref{0068}).
Justification: Convergence, regularity, and quasi-periodicity in \autoref{006F}.
Origin: consequence
---
Let $L\subset\mathbb H$ be a full-rank lattice. For $\lambda\in L^*$ and $q=t+\sum_{j=1}^3e_jx_j$, let the real differential at $\lambda$ act by
$$
dG_\lambda[q]=t\,\partial_tG(\lambda)+\sum_{j=1}^3x_jG_j(\lambda).
$$
For $q\in\mathbb H\setminus L$, form
$$
\zeta_L(q)=G(q)+
\sum_{\lambda\in L^*}
\bigl[G(\lambda+q)-G(\lambda)-dG_\lambda[q]\bigr].
$$
::::

::::lemma \label{006E} | Comparison with the regular linear coordinates
Version: 1
Uses: \autoref{006D}, \autoref{006R}.
Review: pending
Formal: none
Origin: derivation
---
For $\lambda\in\mathbb H\setminus\{0\}$ and $q=t+\sum_{j=1}^3e_jx_j$, put $z_j(q)=te_j-x_j$. Then
$$
dG_\lambda[q]=-\sum_{j=1}^3G_j(\lambda)z_j(q).
$$

:::proof Proof of \ref{006E}
Right regularity gives $\partial_tG(\lambda)=-\sum_jG_j(\lambda)e_j$. Substitute this into the definition of $dG_\lambda[q]$ in \autoref{006D} and use that $t,x_j$ are real.
:::
::::

:::discussion
\autoref{006E} expresses the real Taylor subtraction using regular linear coordinates. The order of quaternionic multiplication is explicit in the formula.
:::

::::proposition \label{006F} | Convergence, derivatives, and quasi-periods
Version: 2
Uses: \autoref{006D}, \autoref{006A}, \autoref{006B}, \autoref{006C}, \autoref{006R}, \autoref{006S}.
Review: pending
Formal: verified
Formal-evidence: [Lean build log](../evidence/lean-EI1-TH1-v1.html#MathResearch.Fueter.E3_v2).
Origin: consequence
---
Let $L\subset\mathbb H$ be a full-rank lattice. The series in \autoref{006D} converges absolutely and locally uniformly on $\mathbb H\setminus L$, as do all its termwise real derivatives. Its sum is odd, is both left and right Fueter-regular, and for $j\in\{1,2,3\}$ satisfies
$$
\partial_{x_j}\zeta_L(q)=\wp_{L,j}(q)\qquad(q\notin L).
$$
There is a unique additive map $\eta_L:L\to\mathbb H$ such that, for every $\omega\in L$ and every $q\notin L$,
$$
\zeta_L(q+\omega)-\zeta_L(q)=\eta_L(\omega).
$$

:::proof Proof of \ref{006F}
Taylor's theorem bounds each bracket, uniformly on a compact set, by $C_K|\lambda|^{-5}$, since the second derivatives of $G$ have degree $-5$. For first derivatives the summands are differences of first derivatives of $G$, again with decay $|\lambda|^{-5}$. Derivatives of order $m\ge2$ have decay $|\lambda|^{-3-m}$. The argument in \autoref{006B} proves convergence and permits all termwise differentiation.

The first Taylor polynomial of a regular function is regular: applying either first-order constant-coefficient operator to it gives that operator applied to $G$, evaluated at $\lambda$, which is zero. The series is therefore left and right regular.

Because $G$ is odd and $dG_{-\lambda}=dG_\lambda$, replacing $\lambda$ by $-\lambda$ proves oddness of $\zeta_L$. Differentiating with respect to $x_j$ gives exactly the defining series for $\wp_{L,j}$, the classical derivative identity [[3, p. 57, following (2.20)]](#ref-krausshar-2004).

Now put $F_\omega(q)=\zeta_L(q+\omega)-\zeta_L(q)$. By \autoref{006C}, all three spatial derivatives of $F_\omega$ vanish. Left regularity also gives
$$
\partial_tF_\omega=-\sum_{j=1}^3 e_j\partial_{x_j}F_\omega=0.
$$
Connectedness of $\mathbb H\setminus L$ makes $F_\omega$ constant. Finally, splitting the increment along $\omega+\nu$ into two increments proves
$$
\eta_L(\omega+\nu)=\eta_L(\omega)+\eta_L(\nu).
$$

The constant increment determines $\eta_L(\omega)$ for each $\omega$, so the resulting map is unique.
:::
::::

:::discussion
The map $\eta_L$ is the first period datum supplied by the construction. Further relations among its values require additional statements and proofs.
:::

## 4. Consequences and examples

::::corollary \label{006G} | Half-period values of zeta
Version: 1
Uses: \autoref{006F}.
Review: pending
Formal: verified
Formal-evidence: [Lean build log](../evidence/lean-EI1-TH1-v1.html#MathResearch.Fueter.E4_v1).
Origin: derivation
---
For a full-rank lattice $L\subset\mathbb H$ and $\omega\in L$ with $\omega/2\notin L$,
$$
\eta_L(\omega)=2\zeta_L(\omega/2).
$$

:::proof Proof of \ref{006G}
Set $q=-\omega/2$ in the quasi-period identity of \autoref{006F} and use the oddness of $\zeta_L$.
:::
::::

::::corollary \label{006H} | Stationary points at half-periods
Version: 1
Uses: \autoref{006B}, \autoref{006C}.
Review: pending
Formal: verified
Formal-evidence: [Lean build log](../evidence/lean-EI1-TH1-v1.html#MathResearch.Fueter.E5_v1).
Origin: derivation
---
Let $L\subset\mathbb H$ be a full-rank lattice. For $j\in\{1,2,3\}$ and $\omega\in L$ with $\omega/2\notin L$, the real differential of $\wp_{L,j}$ vanishes at $\omega/2$:
$$
\partial_{x_\mu}\wp_{L,j}(\omega/2)=0\qquad(\mu=0,1,2,3;\ x_0=t).
$$

:::proof Proof of \ref{006H}
By \autoref{006B} the derivatives exist. Differentiating the two identities in \autoref{006C} shows that each first derivative is odd and $L$-periodic. Its values at $\omega/2$ and $-\omega/2$ are therefore both equal and negatives of one another, so they vanish.
:::
::::

::::corollary \label{006I} | Real dilation
Version: 1
Uses: \autoref{006A}, \autoref{006D}, \autoref{006B}, \autoref{006F}, \autoref{006S}.
Review: pending
Formal: verified
Formal-evidence: [Lean build log](../evidence/lean-EI1-TH1-v1.html#MathResearch.Fueter.E6_v1).
Origin: derivation
---
Let $L\subset\mathbb H$ be a full-rank lattice, $a>0$ a real number, and $j\in\{1,2,3\}$. For all $q\notin L$ and $\omega\in L$,
$$
\begin{aligned}
\wp_{aL,j}(aq)&=a^{-4}\wp_{L,j}(q),\\
\zeta_{aL}(aq)&=a^{-3}\zeta_L(q),\\
\eta_{aL}(a\omega)&=a^{-3}\eta_L(\omega).
\end{aligned}
$$

:::proof Proof of \ref{006I}
Reindex each convergent series using $a\lambda\in aL$ and apply \autoref{006S}. In the zeta subtraction,
$dG_{a\lambda}[aq]=a^{-3}dG_\lambda[q]$, since each first derivative of $G$ has degree $-4$. Thus every bracket has the stated weight. Apply the resulting zeta identity to the difference at $q+\omega$ and $q$ and use \autoref{006F} to obtain the identity for $\eta$.
:::
::::

:::example The standard lattice
For $L_0=\mathbb Z+\mathbb Zi+\mathbb Zj+\mathbb Zk$, \autoref{006C} gives periods $1,i,j,k$. Additivity in \autoref{006F} determines $\eta_{L_0}$ from its four values on these generators.

Since $1/2\notin L_0$, \autoref{006G} gives $\eta_{L_0}(1)=2\zeta_{L_0}(1/2)$ and \autoref{006H} gives $d\wp_{L_0,j}(1/2)=0$ for $j=1,2,3$. The zeta value is expressed by a convergent series here; no numerical evaluation is asserted.
:::

:::discussion
\autoref{006I} describes real dilation. An action by general quaternions requires a separate transformation statement.
:::

\label{006J}

## 5. Further questions

- Which identities relate quasi-periods to the lattice and the kernel's singularity?
- How do extra multiplication symmetries act on these functions?
- How are the lattice coefficients related to harmonic theta series?

These questions are developed as open directions in [Quaternionic Elliptic Coefficients as Lattice Sums](directions.md).

\label{006K}

## Sources and scope

The quaternionic Weierstrass construction is classical work of Fueter. Kraußhar's [[2, §4, p. 1019, eq. (12)]](#ref-krausshar-2001) displays the regularized first-derivative sum and attributes its quaternionic case to Fueter's 1939 paper. See the [literature guide](literature.md#attribution-of-the-construction) for the references and the remaining comparison with Fueter's original notation.

This article supplies explicit arguments for its boxed formulations and makes no novelty claim. Each result carries its own review and formal-verification status.

## Representations and special values of the coefficients

:::discussion
The [higher derivative identities](\ref{0064}) express the regular part of these elliptic functions through convergent lattice sums. Varying the lattice gives [Eisenstein functions on SL₄](lattice-eisenstein-series.md), while [harmonic theta series](lattice-eisenstein-series.md#harmonic-theta-series-and-mellin-integration) express their scalar components through critical L-values.

For a concrete first example, \autoref{00A4} computes the coefficient of $x_1^2$ in the regular part of $\wp_{L_0,1}$ for $L_0=\mathbb Z+\mathbb Zi+\mathbb Zj+\mathbb Zk$ as $96iL(\eta(2\tau)^{12},5)$, with a proof of the exact modular identity and its normalization.

A separate group action, by Möbius transformations of the ball, leads to [discrete series](fueter-discrete-series.md) and the [ordinary Fueter Hardy limit](fueter-hardy-space.md). The connections among these actions are a source of further questions.
:::

## References

1. <span id="ref-fueter-1939"></span> R. Fueter, [*Über vierfachperiodische Funktionen*](https://doi.org/10.1007/BF01696174), Monatshefte für Mathematik und Physik **48** (1939), 161–169.

2. <span id="ref-krausshar-2001"></span> R. S. Kraußhar, [*On a New Type of Eisenstein Series in Clifford Analysis*](https://doi.org/10.4171/ZAA/1057), Zeitschrift für Analysis und ihre Anwendungen **20** (2001), no. 4, 1007–1029. [Open text](https://ems.press/content/serial-article-files/35214).

3. <span id="ref-krausshar-2004"></span> R. S. Kraußhar, [*Generalized Analytic Automorphic Forms in Hypercomplex Spaces*](https://doi.org/10.1007/b95203), Frontiers in Mathematics, Birkhäuser, Basel, 2004.
