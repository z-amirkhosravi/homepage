---
title: Eisenstein and Mellin Formulas for Quaternionic Elliptic Coefficients
description: Eisenstein and harmonic-theta formulas for convergent quaternionic elliptic coefficients, including an explicit cubic-lattice critical value.
section: Quaternionic analysis
article-kind: research
order: 7
---
# Eisenstein and Mellin Formulas for Quaternionic Elliptic Coefficients

\label{009A}



:::discussion
Varying a four-dimensional lattice turns the elliptic coefficients into automorphic functions on a special linear group. We identify both their inducing data and the irreducible module they generate. This is a different group action from the Möbius action on the ball.
:::

## Harmonic numerators of the kernel derivatives

::::lemma \label{009B} | Harmonic numerators in every derivative order
Version: 1
Uses: [Kernel](\ref{006Q}), [multi-indices](\ref{0061}).
Review: pending
Formal: verified
Formal-evidence: [Lean build log](../evidence/lean-EI1-TH1-v1.html#MathResearch.Fueter.EI1_v1).
Origin: derivation
---
For $\nu\in\mathbb N_0^3$, $r=|\nu|$, and $N(q)=|q|^2$, there is a quaternion-valued homogeneous polynomial $H_\nu$ of degree $r+1$, with harmonic real components, such that
$$
G_\nu(q)=\frac{H_\nu(q)}{N(q)^{r+2}}.
$$
It obeys $H_0=\bar q$ and $H_{\nu+e_j}=N\partial_jH_\nu-2(r+2)x_jH_\nu$.

:::proof Proof of \ref{009B}
Start with $H_0=\bar q$. Differentiation gives the recurrence
$$
H_{\nu+e_j}=N\partial_jH_\nu-2(r+2)x_jH_\nu. \label{009C}
$$
It is polynomial and has degree $r+2$. If $H_\nu$ is harmonic of degree $r+1$, then
$$
\Delta(N\partial_jH_\nu)=(4r+8)\partial_jH_\nu,
\qquad \Delta(x_jH_\nu)=2\partial_jH_\nu,
$$
so \eqref{009C} is harmonic. This proves the lemma for every order.
:::
::::

:::discussion
The lattice sums $E_\nu(L)$ and their relation to derivatives of the regular part of $\wp_{L,j}$ are given by the [convergence](\ref{0063}), [coefficient](\ref{0064}) and [parity](\ref{0065}) results. They converge for $r>1$, and even $r$ gives zero. We therefore focus on odd $r\ge3$. Ordinary Taylor coefficients include the multi-index factorials.
:::

## Homogeneous sections and Eisenstein summation

Set $G_4=\mathrm{SL}_4(\mathbb R)$, $\Gamma=\mathrm{SL}_4(\mathbb Z)$, and $K_4=\mathrm{SO}(4)$. Vectors act on the right, and $L_g=\mathbb Z^4g$.

\label{009D}

For real $w>4$, write $I_w$ for the space of smooth functions $f:\mathbb R^4\setminus\{0\}\to\mathbb C$ such that
$$
f(tx)=|t|^{-w}f(x)\qquad(x\ne0,\ t\in\mathbb R^\times).
$$

The condition with $t=-1$ makes every $f\in I_w$ even. The action of $G_4$ is
$$
(R(g)f)(x)=f(xg).
$$
Homogeneity is preserved because $(tx)g=t(xg)$, and $R(g)R(h)=R(gh)$ follows from $(xg)h=x(gh)$.

::::construction \label{009E} | The lattice Eisenstein function
Version: 1
Uses: [homogeneous-function model](\ref{009D}).
Justification: Convergence, smoothness, and equivariance in \autoref{009G}.
Origin: derivation
---
For $w>4$ and $f\in I_w$, form
$$
\mathcal E_f(g)=\sum_{m\in\mathbb Z^4\setminus\{0\}}f(mg).
$$
::::

\label{009F}
Let $e_4=(0,0,0,1)$ and
$$
P=\left\{\begin{pmatrix}A&b\\0&d\end{pmatrix}:\det(A)d=1\right\},
\qquad F_f(g)=f(e_4g).
$$

The primitive-vector regrouping in \autoref{009G} specializes, for a radial section, to the [Epstein–Eisenstein identity](\ref{0099}) [[8, Lemma 2.9]](#ref-sands-2022).

::::theorem \label{009G} | A maximal-parabolic Eisenstein series
Version: 1
Uses: [homogeneous-function model](\ref{009D}), \autoref{009E}.
Review: pending
Formal: none
Origin: derivation
---
For $w>4$, $\mathcal E_f$ is smooth, left $\Gamma$-invariant, of moderate growth with all right derivatives, and satisfies $\mathcal E_{R(h)f}(g)=\mathcal E_f(gh)$. Moreover
$$
\mathcal E_f(g)=2\zeta(w)\sum_{\gamma\in(P\cap\Gamma)\backslash\Gamma}F_f(\gamma g).
$$
The section law is $F_f(pg)=|d|^{-w}F_f(g)$. In normalized left-equivariant/right-translation induction, with $\delta_P(p)=|d|^{-4}$, the inducing character is $\chi(p)=|d|^{2-w}$. For an odd derivative order $r\ge3$, the scalar components of $G_\nu$ give $w=r+3$ and $\chi=|d|^{-(r+1)}$.

:::proof Proof of \ref{009G}
The sum and all its $g$-derivatives converge uniformly on compact subsets of $G_4$: differentiation preserves degree $-w$, and $|mg|\gg_C|m|$ on a compact set $C$. Hence $\mathcal E_f$ is smooth, left $\Gamma$-invariant, and
$$
\mathcal E_{R(h)f}(g)=\mathcal E_f(gh). \label{009H}
$$
Each scalar component of $G_\nu$ is such an $f$, so \autoref{009E} includes the original coefficient sums. The bound $|\mathcal E_f(g)|\le C_f\|g^{-1}\|^w\sum_{m\ne0}|m|^{-w}$, and the same bound for right derivatives, gives moderate growth.

Let $P$ be the maximal parabolic consisting of matrices
$$
p=\begin{pmatrix}A&b\\0&d\end{pmatrix},\qquad \det(A)d=1,
$$
which stabilizes the row line $\mathbb R e_4$. Put $F_f(g)=f(e_4g)$. Then
$$
F_f(pg)=|d|^{-w}F_f(g),\qquad \delta_P(p)=|d|^{-4}. \label{009I}
$$
Every primitive integral row occurs as $e_4\gamma$, and the stabilizer of the primitive line is $P\cap\Gamma$. Grouping a nonzero row by its positive gcd and then identifying opposite primitive rows gives
$$
\boxed{\mathcal E_f(g)=2\zeta(w)
\sum_{\gamma\in(P\cap\Gamma)\backslash\Gamma}F_f(\gamma g).} \label{009J}
$$
This is a maximal-parabolic Eisenstein series in its region of absolute convergence. In the left-equivariant/right-translation convention $F(pg)=\delta_P(p)^{1/2}\chi(p)F(g)$, its **normalized inducing character** is
$$
\chi(p)=|d|^{2-w}=|d|^{-(r+1)}. \label{009K}
$$
Specifying the section law removes any ambiguity from authors who use the inverse character or opposite parabolic.
:::
::::

## The irreducible module selected by the coefficients

\label{009L}
For even $w\ge6$ put $d=w-4$, and let $\mathcal P_d$ be the homogeneous degree-$d$ polynomials on $\mathbb R^4$, with action $p(x)\mapsto p(xg)$. Let $d\sigma$ be Euclidean surface measure on $S^3$.

::::definition \label{009M} | The Vanishing-Moment Subspace
Version: 1
Uses: [homogeneous-function model](\ref{009D}).
---
For even $w\ge6$, the **vanishing-moment subspace** of $I_w$ is
$$
\mathcal M_w=\left\{f\in I_w:\int_{S^3}f(\omega)p(\omega)d\sigma(\omega)=0
\text{ for every }p\in\mathcal P_d\right\}. \label{009N}
$$
::::

Write $\mathcal Y_l$ for complex harmonic homogeneous polynomials of degree $l$ restricted to $S^3$; $V_l=\operatorname{Sym}^l\mathbb C^2$.

::::proposition \label{009P} | Moment kernel and finite-dimensional quotient
Version: 1
Uses: \autoref{009M}, \autoref{009B}.
Review: pending
Formal: none
Origin: derivation
---
For even $w\ge6$, the moment map gives an equivariant exact sequence
$$
0\to\mathcal M_w\to I_w\to\mathcal P_{w-4}^{\vee}\to0.
$$
Its compact-finite kernel is $\bigoplus_{j\ge0}\mathcal Y_{w-2+2j}$. Every scalar derivative kernel of order $r=w-3$ lies in its minimal compact type $\mathcal Y_{w-2}$.

:::proof Proof of \ref{009P}
The pairing is bilinear, not Hermitian. Since the product has degree $-4$, angular change of variables under $g\in\mathrm{SL}_4$ shows
$$
\int_{S^3}f(\omega g)p(\omega g)d\sigma(\omega)
=\int_{S^3}f(\omega)p(\omega)d\sigma(\omega).
$$
Indeed for $\eta=\omega g/|\omega g|$, $d\sigma(\eta)=|\omega g|^{-4}d\sigma(\omega)$. Thus \eqref{009N} is invariant, and the pairing induces an exact sequence
$$
0\longrightarrow\mathcal M_w\longrightarrow I_w
\longrightarrow\mathcal P_{w-4}^{\vee}\longrightarrow0. \label{009Q}
$$
Surjectivity follows from the nondegenerate spherical pairing on the finite-dimensional polynomial space. Harmonic decomposition of $\mathcal P_{w-4}$ gives
$$
(\mathcal M_w)_{K_4}=\bigoplus_{j\ge0}\mathcal Y_{w-2+2j}, \label{009R}
$$
where the subscript means $K_4$-finite vectors. The low harmonics $\mathcal Y_0,\mathcal Y_2,\ldots,\mathcal Y_{w-4}$ constitute the finite-dimensional quotient. By \autoref{009B}, every scalar Fueter kernel derivative of order $r=w-3$ belongs to the **minimal compact type** $\mathcal Y_{w-2}$ of this kernel.
:::
::::

For the general real degenerate principal series, see [[5, Thms. 1.1–1.2]](#ref-gourevitch-2017). With normalized $P_{3,1}$ induction, the restriction of $|\det|^{w-2}\times1$ to $\mathrm{SL}_4(\mathbb R)$ has the section law $|d|^{-w}$. \autoref{009S} gives the harmonic-transition argument for this restriction.

::::theorem \label{009S} | Irreducibility and harmonic transitions
Version: 1
Uses: \autoref{009P}, irreducibility of spherical harmonics under $\mathrm{SO}(4)$.
Review: pending
Formal: none
Origin: derivation
---
The $(\mathfrak{sl}_4,\mathrm{SO}(4))$-module $(\mathcal M_w)_{K_4}$ is irreducible for every even $w\ge6$. Its compact types are
$$
\bigoplus_{j\ge0}\mathcal Y_{w-2+2j}\simeq
\bigoplus_{j\ge0}V_{w-2+2j}\boxtimes V_{w-2+2j}.
$$

:::proof Proof of \ref{009S}
For a symmetric trace-free real matrix $A$, write
$$
Q_A(x)=xAx^t,\quad D_AH=(xA)\cdot\nabla H,
\quad T_AH=\sum_{ij}A_{ij}\partial_i\partial_jH.
$$
Represent a compact type $H\in\mathcal Y_l$ by $f_H(x)=|x|^{-w-l}H(x)$. On $S^3$ the infinitesimal action is
$$
dR(A)H=D_AH-(w+l)Q_AH. \label{009T}
$$
It has harmonic degrees $l+2,l,l-2$. Its projection onto degree $l-2$ is exactly
$$
\operatorname{pr}_{l-2}dR(A)H
=\frac{l+2-w}{4l(l+1)}T_AH. \label{009U}
$$
To see this, $\Delta D_AH=2T_AH$ and $\Delta^2(Q_AH)=8T_AH$. Harmonic decomposition therefore gives degree-$l-2$ terms $T_AH/(2l)$ in $D_AH|_{S^3}$ and $T_AH/[4l(l+1)]$ in $(Q_AH)|_{S^3}$, yielding \eqref{009U}. The degree-$l+2$ term is $-(w+l)$ times the top harmonic part of $Q_AH$.

The lowering map vanishes precisely at $l=w-2$ and is nonzero at every subsequent degree in \eqref{009R}; the raising map is nonzero at every degree. Nonzeroness can be seen over the complexified Lie algebra by taking $H=(x_1+ix_2)^l$ and quadratic forms $(x_1\pm ix_2)^2$: the plus choice raises harmonically, the minus choice gives a nonzero $T_AH$ when $l\ge2$. Each $\mathcal Y_l$ is an irreducible $K_4$-module of multiplicity one. Any nonzero submodule contains a compact type; successive nonzero lowering and raising maps then give all of \eqref{009R}. This proves irreducibility. The identification $\mathcal Y_l\simeq V_l\boxtimes V_l$ follows from the usual $\operatorname{Spin}(4)$ harmonic-polynomial representation; $(-1,-1)$ acts trivially.
:::
::::

## Nonvanishing and the automorphic realization

::::theorem \label{009V} | The coefficient-generated automorphic module
Version: 1
Uses: \autoref{009B}, \autoref{009G}, \autoref{009S}.
Review: pending
Formal: none
Origin: derivation
---
For odd $r\ge3$, the scalar components of $g\mapsto E_\nu(\mathbb Z^4g)$, $|\nu|=r$, generate an automorphic $(\mathfrak{sl}_4,\mathrm{SO}(4))$-module isomorphic to $(\mathcal M_{r+3})_{K_4}$. The Eisenstein map is injective on this module. Its minimal compact type is $\mathcal Y_{r+1}$.

:::proof Proof of \ref{009V}
An intertwining sum could conceivably vanish on the entire module, so this needs a proof. Choose $H\in\mathcal Y_{w-2}$ with $H(e_4)\ne0$, and put
$$
g_a=\operatorname{diag}(a,a,a,a^{-3}),\quad a\to\infty,
\qquad f_H(x)=|x|^{-2w+2}H(x).
$$
The rows $(0,0,0,k)$ contribute exactly $2\zeta(w)a^{3w}H(e_4)$. All other rows satisfy $|f_H(x)|\le C|x|^{-w}$. For $m'\ne0$,
$$
\sum_{k\in\mathbb Z}(a^2|m'|^2+a^{-6}k^2)^{-w/2}
\ll a^{-w}|m'|^{-w}+a^{4-w}|m'|^{1-w}.
$$
Both sums over $m'\in\mathbb Z^3\setminus0$ converge for $w>4$. Consequently
$$
\mathcal E_{f_H}(g_a)=2\zeta(w)a^{3w}H(e_4)+O(a^{4-w}). \label{009W}
$$
The Eisenstein map is nonzero on the minimal type, hence injective on the irreducible module \eqref{009R}. The scalar components of the order-$r$ kernel derivatives contain a nonzero element of that type: for example $\partial_x^rG(ix)=-i(-1)^r(3)_r x^{-r-3}$ for $x>0$. Its compact orbit spans the type and its enveloping-algebra orbit spans \eqref{009R}.
:::
::::

:::discussion
The fixed-order coefficients occupy the minimal compact type. General $\mathrm{SL}_4$ transformations generate the larger space \eqref{009R}; they do not preserve the flat Fueter equation or act within the finite tuple of coefficients.

This specifies an irreducible real-place Harish-Chandra module. It does not assert a unitary $L^2(\Gamma\backslash G_4)$ realization or a discrete series of $\mathrm{SL}_4$. The proof concerns the algebraic module of $K$-finite automorphic functions; a choice of globalization/topology or an adelic classification with finite-place constituents is additional work. A coefficient can vanish at a particular symmetric lattice even though the automorphic function is nonzero. For example cubic-lattice symmetries force numerous components to vanish.
:::

::::corollary \label{009X} | The first nonzero derivative order
Version: 1
Uses: \autoref{009P}, \autoref{009V}.
Review: pending
Formal: none
Origin: derivation
---
For $r=3$, the inducing degree is $-6$, the normalized character is $|d|^{-4}$, the minimal compact type is $V_4\boxtimes V_4$ of dimension $25$, and the finite-dimensional quotient of $I_6$ is $\mathcal P_2^\vee$ of dimension $10$.

:::proof Proof of \ref{009X}
Insert $w=6$ in the [moment-quotient calculation](\ref{009P}), the [harmonic-transition calculation](\ref{009S}) and the [automorphic realization](\ref{009V}). The dimensions are $(4+1)^2=25$ and $\binom{2+4-1}{3}=10$.
:::
::::

## Rotation covariance of the coefficient tuple

::::proposition \label{009Y} | The coefficient action descends to the rotation group
Version: 1
Uses: [Convergent sums](\ref{0063}).
Review: reviewed
Review-evidence: [Proof correspondence review](../evidence/lean-proof-correspondence.html#arguments-and-background-results)
Formal: verified
Formal-evidence: [Lean build log](../evidence/lean-DS3-DS4-verified.html#MathResearch.Fueter.EI7_v1)
Origin: derivation
---
Let $U_{-r-3}$ be the right-$\mathbb H$ span of the order-$r$ kernel derivatives, with $r>1$, and let $\rho(a,b)f(q)=bf(a^{-1}qb)$ for unit quaternions $a,b$. Set $\alpha_L(f)=\sum_{\lambda\ne0}f(\lambda)$. Then
$$
(\sigma(a,b)\alpha)(f)=b\alpha(\rho(a,b)^{-1}f),\qquad
\alpha_{aLb^{-1}}=\sigma(a,b)\alpha_L.
$$
This is a genuine real representation on right-$\mathbb H$-linear functionals and factors through $\mathrm{SO}(4)$.

:::proof Proof of \ref{009Y}
The identity $G(a^{-1}qb)=b^{-1}G(q)a$ follows directly from the kernel formula. Differentiate it in any real coordinate directions. The chain rule expresses rotated order-$r$ derivatives using all four real derivative directions, with constant right quaternion factors. The kernel is also right regular: direct differentiation gives $\partial_tG+\partial_xG\,i+\partial_yG\,j+\partial_zG\,k=0$. This identity, and its derivatives, eliminate every time derivative in favor of spatial derivatives with right coefficients. Thus $U_{-r-3}$ is invariant under $\rho$. The formula for $\rho$ gives its group law and right-$\mathbb H$ linearity. Reindexing the absolutely convergent sum gives the displayed identity. For composition, the two output factors multiply as $b_1b_2$, and the precomposition is $\rho(k_2^{-1})\rho(k_1^{-1})=\rho((k_1k_2)^{-1})$. At $(-1,-1)$, the input representation is $-1$, while the output also gets $-1$, so $\sigma(-1,-1)\alpha(f)=-\alpha(-f)=\alpha(f)$. The [kernel of $\operatorname{Spin}(4)\to\mathrm{SO}(4)$](\ref{00BH}) therefore acts trivially.
:::
::::

:::discussion
The arithmetic quotient is $\Gamma\backslash G_4/K_4$; lattice stabilizers give the usual orbifold interpretation. The scalar-component model above avoids choosing local frames. The underlying induced representations are part of the theory studied by [[5]](#ref-gourevitch-2017); the proofs here specify our conventions directly. For the standard primitive-vector identity compare [[8]](#ref-sands-2022), §2.5. The following sections give the theta and special-value interpretation, including the cubic example.
:::


The following sections express the quaternionic elliptic coefficients as Mellin transforms of harmonic theta series. The classical [theta transformation and scalar modularity theorems](harmonic-theta-modularity.md) supply their modular interpretation. On the cubic lattice, the explicit numerator calculation identifies a coefficient with a nonzero critical value of the weight-six newform $\eta(2\tau)^{12}$.

## Harmonic theta series and Mellin integration

Let $L\subset\mathbb R^4$ be a full Euclidean lattice, $H$ a scalar homogeneous harmonic polynomial of even degree $\ell>0$, and $N(x)=|x|^2$.
In this article, $L^*$ denotes the Euclidean dual lattice. For an even integral lattice put $Q=N/2$ and $D=L^*/L$. In this case $\mu$ ranges over $D$, and $L+\mu$ denotes the corresponding coset in $L^*$.

::::definition \label{009Z} | Harmonic Theta Functions
Version: 1
Uses: [Harmonic numerators](\ref{009B}).
---
The **harmonic theta function** is
$$
\theta_{L,H}(it)=\sum_{\lambda\in L}H(\lambda)e^{-\pi tN(\lambda)}\quad(t>0).
$$
If the Euclidean bilinear form is integral on $L$ and $N(\lambda)$ is even for every $\lambda\in L$, the **coset theta functions** are
$$
\Theta_\mu(\tau)=\sum_{\lambda\in L+\mu}H(\lambda)e^{2\pi i\tau Q(\lambda)},\quad
\Theta_{L,H}=\Theta_0,\quad \operatorname{Im}\tau>0.
$$
::::

Since $Q$ is integral on $L$, the zero component has integral exponents; for $\Theta_{L,H}=\sum_{m\ge1}a_me^{2\pi im\tau}$ put $L(\Theta_{L,H},s)=\sum_{m\ge1}a_mm^{-s}$ wherever absolutely convergent.

The [scalar modularity theorem](\ref{008G}) gives the level and character of $\Theta_{L,H}$ for an even integral lattice. Its normalization is $Q=N/2$, as here.

::::theorem \label{00A0} | A convergent Mellin formula for each elliptic coefficient
Version: 1
Uses: \autoref{009Z}, \autoref{009B}, \autoref{0063}.
Review: pending
Formal: verified
Formal-evidence: [Lean build log](../evidence/lean-EI1-TH1-v1.html#MathResearch.Fueter.TH1_v1).
Origin: derivation
---
Let $\nu\in\mathbb N_0^3$ have odd order $r\ge3$, and let $H$ be any real component of the numerator $H_\nu$. For every full Euclidean lattice $L$,
$$
E_{\nu,H}(L):=\sum_{\lambda\ne0}\frac{H(\lambda)}{N(\lambda)^{r+2}}
=\frac{\pi^{r+2}}{\Gamma(r+2)}\int_0^\infty t^{r+1}\theta_{L,H}(it)\,dt.
$$
Both the lattice sum and the interchange of summation and integration are absolutely convergent.

:::proof Proof of \ref{00A0}
The numerator has degree $r+1$. Thus each absolute summand is bounded by a constant times $|\lambda|^{-r-3}$, whose exponent exceeds the lattice dimension four. The gamma integral gives, for $s=r+2$,
$$
\sum_{\lambda\ne0}|H(\lambda)|\int_0^\infty t^{s-1}e^{-\pi tN(\lambda)}dt
=\frac{\Gamma(s)}{\pi^s}\sum_{\lambda\ne0}\frac{|H(\lambda)|}{N(\lambda)^s}<\infty.
$$
Fubini's theorem now gives the formula. The argument also applies to any homogeneous harmonic numerator of degree $r+1$, including linear combinations of the kernel numerators.
:::
::::


::::corollary \label{00A1} | Critical values with all normalizing factors fixed
Version: 1
Uses: \autoref{00A0}, [scalar theta modularity](\ref{008G}).
Review: pending
Formal: none
Origin: derivation
---
Under \autoref{00A0}'s hypotheses, if $L$ is even integral, then
$$
E_{\nu,H}(L)=2^{-(r+2)}L(\Theta_{L,H},r+2).
$$
The theta form has weight $k=r+3$, and the evaluation point is $k-1$. In particular the first potentially nonzero coefficients, of order $r=3$, evaluate weight-six cusp forms at $s=5$.

:::proof Proof of \ref{00A1}
Group the absolutely convergent lattice sum by $m=Q(\lambda)$ and use $N(\lambda)=2m$. This gives exactly the factor $2^{-(r+2)}$. The [scalar modularity theorem](\ref{008G}) applies to the harmonic numerator of degree $\ell=r+1$ and gives cuspidality and weight $2+\ell=r+3$. The usual critical integers for the weight-$k$ holomorphic cusp-form $L$-function are $1,\ldots,k-1$, from the archimedean gamma factors in the functional equation; hence this is the upper critical value in the classical normalization. No Hecke-eigenform hypothesis is required for the identity.
:::
::::

## The cubic lattice and a weight-six newform

\label{00A2}

Let $L_0=\mathbb Z+\mathbb Zi+\mathbb Zj+\mathbb Zk$ and put
$$
H_4(t,x,y,z)=t^4+x^4+y^4+z^4-\frac12(t^2+x^2+y^2+z^2)^2.
$$
In this example the Fourier exponent uses $Q_0(m)=|m|^2$, rather than $N/2$:
$$
\vartheta(\tau)=\sum_{m\in\mathbb Z^4}H_4(m)e^{2\pi i\tau|m|^2},\qquad
f(\tau)=\eta(2\tau)^{12}.
$$
Here $u=e^{2\pi i\tau}$ and $\eta(\tau)=u^{1/24}\prod_{n\ge1}(1-u^n)$. Expanding the product gives
$$
f(\tau)=u\prod_{n\ge1}(1-u^{2n})^{12}
=u-12u^3+54u^5-88u^7-99u^9+\cdots.
$$
For this Fourier convention $L(f,s)=\sum_{m\ge1}a_mm^{-s}$ when $f=\sum a_mu^m$.

::::theorem \label{00A3} | The exact harmonic theta identity
Version: 1
Uses: [The cubic-lattice conventions](\ref{00A2}), [scalar theta modularity](\ref{008G}), the eta-quotient and dimension formulas cited in the proof.
Review: pending
Formal: none
Origin: consequence
---
One has
$$
\vartheta(\tau)=4\eta(2\tau)^{12},\qquad
\sum_{m\in\mathbb Z^4\setminus\{0\}}\frac{H_4(m)}{|m|^{10}}=4L(f,5).
$$
The normalized eta product $f$ is the unique newform in $S_6(\Gamma_0(4))$, with trivial character.

:::proof Proof of \ref{00A3}
First $\Delta\sum x_j^4=12N$ and $\Delta(N^2)=24N$, so $H_4$ is harmonic. Apply the [scalar modularity theorem](\ref{008G}) [[9, Thm. 4]](#ref-simard-2015) to the even lattice $L=\sqrt2L_0$, whose Gram matrix is $A=2I_4$. Its level is four: $4A^{-1}=2I_4$ is even integral, whereas $2A^{-1}=I_4$ is not even. Moreover $\det A=16$, so the character $\big(16/\cdot\big)$ is trivial on $\Gamma_0(4)$.

The normalization $Q(x)=|x|^2/2$ on $L$ gives $Q(\sqrt2m)=|m|^2$, and $H_4(\sqrt2m)=4H_4(m)$. Thus $\Theta_{L,H_4}=4\vartheta$. The theorem gives $\Theta_{L,H_4}\in S_6(\Gamma_0(4))$, and hence $\vartheta\in S_6(\Gamma_0(4))$.

For the eta product use the eta-quotient criterion and cusp-order formula [[1, Thms. 2.4–2.5]](#ref-eta-quotients-2018). For $\prod_{\delta\mid N}\eta(\delta\tau)^{r_\delta}$ the weight is $\tfrac12\sum r_\delta$, the congruences are $\sum\delta r_\delta\equiv\sum(N/\delta)r_\delta\equiv0\pmod{24}$, and the character is the Kronecker symbol associated to $(-1)^k\prod\delta^{r_\delta}$. Here $N=4$, $r_2=12$, and both sums equal $24$. The character is trivial since $2^{12}$ is a square. At a cusp of denominator $c\mid4$ the order is
$$
\frac4{24}\sum_{\delta\mid4}
\frac{\gcd(c,\delta)^2r_\delta}{\gcd(c,4/c)c\delta}=1
\quad(c=1,2,4).
$$
Thus $f$ is a nonzero cusp form of the same weight, level, and character.

The dimension formula [[3, Thm. 3.5.1]](#ref-diamond-shurman-2005), for even $k>2$, is
$$
\dim S_k(\Gamma)=(k-1)(g-1)+(k/2-1)c
+\lfloor k/4\rfloor e_2+\lfloor k/3\rfloor e_3.
$$
For $\Gamma_0(4)$ the index is six, there are three cusps, no elliptic points, and genus zero. The formula gives $-5+2\cdot3=1$. For level one the data $(g,c,e_2,e_3)=(0,1,1,1)$ give dimension zero in weight six; for level two the data $(0,2,1,0)$ also give zero. Therefore there is no oldspace at level four.

The eight shortest lattice vectors have $H_4=1/2$, so the first coefficient of $\vartheta$ is four. The first coefficient of $f$ is one. Equality follows from the one-dimensional cusp space. Its normalized generator is a Hecke eigenform and is new because the oldspace is zero. Finally group the absolutely convergent harmonic lattice sum by $|m|^2$ to obtain $L(\vartheta,5)=4L(f,5)$; \autoref{00A0}'s convergence estimate applies to any harmonic quartic.
:::
::::

::::theorem \label{00A4} | An individual quaternionic elliptic coefficient
Version: 1
Uses: \autoref{00A3}, \autoref{0064}, \autoref{0063}.
Review: pending
Formal: none
Origin: derivation
---
With $G(q)=\bar q/|q|^4$, spatial derivative $\partial_x$ in the $i$ direction, and the cubic lattice $L_0$,
$$
E_{(3,0,0)}(L_0)=\sum_{\lambda\ne0}\partial_x^3G(\lambda)
=192\,i\,L\!\left(\eta(2\tau)^{12},5\right)\ne0.
$$
For the elliptic function $\wp_{L_0,1}$ of \autoref{006A}, the coefficient of $x^2$ in the real Taylor expansion of its regular part $\wp_{L_0,1}-G_1$ at zero is $96iL(f,5)$.

:::proof Proof of \ref{00A4}
Differentiate the $i$ component $-x/N^2$ of $G$ three times. It gives
$$
\frac{12N^2-144x^2N+192x^4}{N^5}.
$$
The real, $j$, and $k$ components have a coordinate of odd parity and vanish after summation over the sign-symmetric lattice. Absolute convergence justifies these cancellations and coordinate permutations. Average the displayed numerator over the four coordinate positions; its lattice sum is unchanged, while its value becomes
$$
12N^2-36N^2+48(t^4+x^4+y^4+z^4)=48H_4.
$$
\autoref{00A3} therefore gives $E_{(3,0,0)}=48i\cdot4L(f,5)$. The Mellin identity
$$
L(f,5)=\frac{(2\pi)^5}{\Gamma(5)}\int_0^\infty f(it)t^4dt
$$
follows by the same absolute integration argument as \autoref{00A0} (the harmonic coefficient sum converges at five). Every factor of $\eta(2it)^{12}$ is positive for $t>0$, so this value is strictly positive. Finally \autoref{0064} with $\mu=(2,0,0)$ gives the second derivative of the regular part. Division by $2!$ gives its ordinary Taylor coefficient.
:::
::::


\label{00A5}


## The Automorphic Representation of the Cubic Example

The preceding calculation identifies $f=\eta(2\tau)^{12}$ as a normalized newform of exact level four, weight six and trivial character. By the classical newform correspondence [[4, Thm. 2.2, Prop. 2.15]](#ref-feng-adelization), its adelization generates an irreducible cuspidal representation $\pi_f$ of $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ with conductor four and trivial central character. Its archimedean factor is the weight-six discrete series; on restriction to $\mathrm{SL}_2(\mathbb R)$, the holomorphic summand has lowest weight six.

For the finite standard $L$-function in unitary normalization,
$$
L(f,s)=L(\pi_f,s-5/2).
$$
The shift is $(6-1)/2$. Thus the coefficient in \autoref{00A4} is $192iL(\pi_f,5/2)$, while its classical modular-form expression is $192iL(f,5)$.

## How the representations fit together

:::discussion
| Object varied | Group | Result established here |
| --- | --- | --- |
| A regular function on the ball, with its point moved by Möbius transformations | $\mathrm{Sp}(1,1)$ | [Discrete series](fueter-discrete-series.md) for compatible spinors; the [Hardy limit](fueter-hardy-space.md) for one quaternionic value. |
| The lattice in a kernel-derivative sum | $\mathrm{SL}_4(\mathbb R)$ | An [irreducible module of Eisenstein functions](\ref{009V}). |
| The modular variable of the cubic harmonic theta form | $\mathrm{GL}_2$, or the classical modular group | [The cubic calculation](\ref{00A3}) and [its automorphic interpretation](\ref{00A5}) identify a weight-six newform and its critical value. |

The theta and Mellin formulas provide the stated numerical bridge. An equivalence or functorial correspondence between the first two representations has not been established. An arbitrary lattice theta form need not be an eigenform and may vanish; the cubic example succeeds because its cusp space has dimension one. Its newform data also agree with [[6, 4.6.a]](#ref-lmfdb-46a).
:::

## Questions opened by the example

:::discussion
Which other arithmetic lattices and individual quaternionic coefficients select a single newform? Can lattice symmetries predict vanishing or isolate Hecke constituents? What algebraic periods normalize the resulting critical values, and how do these values interact with quaternionic multiplication? These questions remain open here.

At derivative order $r=1$, the predicted theta weight is four and the evaluation point is three. \autoref{00A0} does not apply: the original lattice sum is at the boundary of absolute convergence. Cuspidality still makes the theta Mellin integral meaningful on an even integral lattice, but comparison with a specified regularization or with elliptic quasi-periods needs a separate proof.
:::


## Related Results

\label{00A6}

[Modularity and cuspidality of the coset vector](\ref{008D}).

## References

1. <span id="ref-eta-quotients-2018"></span> Allison Arnold-Roksandich, Kevin James and Rodney Keaton, [*Counting eta-quotients of prime level*](https://msp.org/involve/2018/11-5/involve-v11-n5-p08-p.pdf), Involve **11** (2018), no. 5, 827–844.

2. <span id="ref-cohen-stromberg-2017"></span> Henri Cohen and Fredrik Strömberg, [*Modular Forms: A Classical Approach*](https://doi.org/10.1090/gsm/179/10), Graduate Studies in Mathematics, vol. 179, AMS, 2017.

3. <span id="ref-diamond-shurman-2005"></span> Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics, vol. 228, Springer, New York, 2005.

4. <span id="ref-feng-adelization"></span> Tony Feng, [*Relation between classical modular forms and automorphic representations*](https://virtualmath1.stanford.edu/~conrad/conversesem/Notes/L24.pdf), lecture notes.

5. <span id="ref-gourevitch-2017"></span> Dmitry Gourevitch, [*Composition Series for Degenerate Principal Series of GL(n)*](https://mathreports.ca/article/composition-series-for-degenerate-principal-series-of-gln/), C. R. Math. Rep. Acad. Sci. Canada **39** (2017), no. 1, 1–12. [Author version](https://arxiv.org/abs/1510.05255).

6. <span id="ref-lmfdb-46a"></span> The LMFDB Collaboration, [weight-six, level-four space 4.6.a](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/4/6/a/).

7. <span id="ref-ono-2004"></span> Ken Ono, [*The Web of Modularity: Arithmetic of the Coefficients of Modular Forms and q-series*](https://doi.org/10.1090/CBMS/102), CBMS Regional Conference Series in Mathematics, vol. 102, American Mathematical Society, Providence, RI, 2004.

8. <span id="ref-sands-2022"></span> Adrienne Sands, [*Automorphic Hamiltonians, Epstein Zeta Functions, and Kronecker Limit Formulas*](https://arxiv.org/abs/2208.02082v1), arXiv:2208.02082v1 (2022).

9. <span id="ref-simard-2015"></span> Nicolas Simard, [*Notes on theta series*](https://www.math.mcgill.ca/goren/GS/Thetas.pdf), lecture notes, 2 November 2015.
