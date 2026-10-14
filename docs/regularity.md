# Interior small-energy regularity: statements and proof

The development concerns locally energy-minimizing maps on open Euclidean
domains, with a compact smooth embedded target and its induced metric. It
proves a unique smooth representative on the inner half ball whenever the
normalized energy is below one fixed threshold. The complete argument uses
the same map, target and displayed weak gradient throughout.

## Mathematical objects and normalization

`HarmonicMaps.Domain n` and `Ambient q` are finite-dimensional Euclidean spaces.
A gradient is a family of coordinate columns. Its native Pi norm differs from
its Hilbert–Schmidt norm; energy is the actual sum of squared column norms:

$$E(u;B)=\int_B\sum_{i=1}^n|D_i u|^2,\qquad
\Theta_u(a,R)=R^{2-n}E(u;B_R(a)).$$

Higher derivative bounds use native multilinear operator norms. The forcing
sign is $\Delta u=F$, expressed weakly by
$\int Du:D\psi=-\int F\cdot\psi$ for compact smooth tests.

Local minimality quantifies over genuine Sobolev, target-valued competitors
whose difference lies in the native $W^{1,2}_0$ closure. The target structure
supplies compactness and smooth embeddedness. Projection, first and second
projection derivatives, and the variation identities are proved from these
data. No elliptic regularity estimate is a field of the minimizer or target.

The continuous representative agrees with the original Sobolev map almost
everywhere. Its uniqueness is on the source open ball. Ambient extensions
outside that ball are not specified by the theorem.

## Energy decay and the Hölder representative

The proof in [OriginalProof.tex](../sources/OriginalProof.tex) establishes
stationarity from local minimality, exact normalized-energy monotonicity and
both fixed and variable smoothing. The variable-radius derivative retains the
full matrix $I-y\otimes Ds$ and determinant $1-Ds\cdot y$. Sobolev density and
actual zero-boundary closure justify the admissible competitors.

The uniform smoothing scales are $\bar h=\eta^{1/4}$,
$\delta=\eta^{1/8}$ and $\tau=\eta^{1/(64(n-1))}$. Monotonicity supplies
$|Dm_h|^2\le C\eta h^{-2}$, which supports these choices in every $n\ge2$.
The Poisson Dirichlet construction has the closed-ball regularity and actual
surface-measure normalization needed for Green identities and comparison.

Projected competitors and minimality yield one-step energy contraction.
Affine transport, geometric-scale iteration, the Sobolev Poincaré inequality
and differentiation of ball averages then produce the Hölder representative,
its almost-everywhere identity, pointwise target values and local uniqueness.

## C1 regularity from the actual weak equation

The upgrade manuscript is
[holder_to_ck_regularity.tex](../sources/holder_to_ck_regularity.tex). The target
projection provides a fixed smooth quadratic coefficient $A$, with the signed
weak equation

$$\Delta w=F,\qquad F=\sum_i A(w)[D_iw,D_iw].$$

A continuous Sobolev harmonic replacement has the original boundary data,
a genuine zero-boundary difference and coefficient-one energy orthogonality.
If $[w]_\alpha\le H$ and $|F|\le K|Dw|_{\mathrm{HS}}^2$, the difference obeys

$$\int_{B_r}|D(w-h)|_{\mathrm{HS}}^2
\le2KH r^\alpha\int_{B_r}|Dw|_{\mathrm{HS}}^2.$$

Smooth approximation and signed weak Poisson mollification establish this
identity and estimate for the original rough gradient. The comparison gives
all-radius energy growth with exponent $n-\alpha/2$ and gradient-excess growth
with exponent $n+\alpha/4$. Campanato reconstruction produces all-radius limits
of the actual gradient means, with exponent $\gamma=\alpha/8$.

The reconstructed gradient agrees almost everywhere with the original weak
gradient. Interior mollification and uniform derivative convergence identify
it with the actual Fréchet derivative of the same $w$. This also proves the
segment identity. C1 maps provide native local Sobolev data with their actual
classical coordinate derivatives.

## The proved Poisson Schauder estimate

The fundamental solution uses its punctured Euclidean carrier. The two-
dimensional logarithm and the higher-dimensional power have the actual sphere
normalization and flux. The Hessian kernel has exact annular cancellation.
Its principal-value distributional identity includes the positive
$\delta_{ij}/n$ point-evaluation term.

Near/far cancellation bounds retain the full input Hölder exponent. Uniform
limits of smooth Newtonian potentials identify both derivatives of the same
potential. The continuous weakly harmonic remainder is smooth by its local
radial mean representation. These constructions give C2 regularity, interior
operator-norm and Hölder estimates, and the original pointwise Poisson equation.

Actual affine weak-data transport gives arbitrary-ball estimates with exact
radius powers. On nested balls, local bounds control close pairs and the
supremum controls far pairs, retaining the full exponent.

## One threshold and all positive derivative orders

The energy threshold is selected before every map and order. It combines the
Hölder representative threshold, the C1 small-Hölder threshold and $E\le1$.
Thus the small parameter $\delta=\sqrt E$ obeys $0\le\delta\le1$.

A fixed compact target neighborhood supplies one sequence of coefficient
bounds. Every derivative of the quadratic forcing retains two positive-order
derivative factors, so its norm and Hölder estimates remain at scale
$\delta^2$. Lower-order Hölder control follows from the next actual derivative
on a convex ball.

For $m\ge1$, use

$$s_m=\frac12+\frac18\,2^{-(m-1)}.$$

The same map has $C^{m,\gamma}$ control on $B_{s_m}$. Its coordinate derivatives
of order $m-1$ satisfy the differentiated signed weak equations with genuine
C1 Sobolev data. Nested-radius Schauder estimates and finite
coordinate-to-operator reconstruction give the next order with

$$\|w-w(0)\|_{C^{m+1,\gamma}(B_{s_{m+1}})}
\le S_m(M_m\delta+P_m\delta^2)
\le S_m(M_m+P_m)\delta.$$

The recursive constants include all lower-order bounds and are fixed before
the map and its energy.
Every finite order restricts to the same half-ball representative, giving
smoothness without a new threshold. Zero energy has zero right-hand sides in
all the actual derivative bounds.

## Affine scaling and the source seminorm

The forward and inverse affine maps preserve Sobolev data, target membership,
all local competitors and the displayed weak gradient. At radius $R$,
$E(u(a+R\,\cdot);B_1)=\Theta_u(a,R)$. A slightly larger contained closed ball
provides the open domain needed by the unit argument while the dilation stays
at the original $R$.

For the same smooth representative, inverse affine differentiation gives
$D^kw(x)=R^{-k}D^k\widetilde w((x-a)/R)$ and

$$[D^kw]_{\gamma;B_{R/2}(a)}
=R^{-(k+\gamma)}[D^k\widetilde w]_{\gamma;B_{1/2}}.$$

`HolderToCK.holderSeminorm` is the extended nonnegative supremum of the actual
quotients over distinct pairs. Unbounded quotients give infinity. Its finite
bounds are exactly `HolderBoundOn`; the real value is used only after
finiteness has been proved. The affine pair bijection proves the exact full
supremum equality on the same smooth carrier.

## Verification and reuse

The two libraries belong to one Lake package and share all foundational
objects. `HarmonicMaps.Regularity` exposes both the Hölder theorem and the
complete smooth theorem; `HolderToCK.Regularity` also exposes the generic C1,
Schauder and local quadratic-Poisson smoothness results.

The public checks compare the complete types of 15 theorem exports with fixed
baselines, check the source and foundational-definition fingerprints, scan both
libraries for proof gaps and trust bypasses, and inspect the advertised
proof dependency closures. The kernel replay checks compiled declarations.
Run the commands in the [README](../README.md) after the full default build.
