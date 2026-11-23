# The scaled formulas for primes: energy, acceleration, mass

Three formulas, one constant, and a clear line around what each one may be used for. Proved in
[`prime-scales.lean`](prime-scales.lean) (10 theorems), measured in `scripts/prime_scales.py`,
[`tableV12_prime_scales.csv`](tableV12_prime_scales.csv).

With $t=\log p$ and the twin constant $C_2=0.6601618158468696$:

$$\boxed{\ \hat E=\frac{\text{gap}}{t^{2}}=\frac{1}{2C_2}=0.757390\pm0.000018\ },\qquad
\boxed{\ a=\frac{1}{C_2}=2\hat E=1.514780\ },\qquad
\boxed{\ \hat m=\frac{T}{t^{2}}=\frac{1}{2C_2}+\frac{2}{t^{2}}\ }$$

| symbol | is | units | status |
|---|---|---|---|
| $\hat E$ | the energy per handoff, per unit $\log^2p$ | dimensionless (span per $\log^2p$) | **measured** to 0.001% from $10^{4}$ to $10^{12}$ |
| $a$ | the acceleration in the $(\log p,\ \text{span})$ plane | dimensionless | **definition** from $\hat E$ by $E=\tfrac12at^2$ |
| $\hat m$ | the "rest mass" of a handoff, per unit $\log^2p$ | dimensionless | **exact** given the law; the $2/t^2$ is the pair |
| $T=\text{gap}+2$ | the handoff's total gap | integers | the pair plus the air |

## 1. The scaled trio, decade by decade

| window | handoffs | $\hat E$ | $a=2\hat E$ | $\hat m$ | $\rho$ (pairs/span) | $2C_2/\langle t^2\rangle$ |
|---|---|---|---|---|---|---|
| $10^{4}$–$10^{5}$ | 1,019 | 0.766568 | 1.533136 | 0.783730 | 1.131e−2 | 1.147e−2 |
| $10^{5}$–$10^{6}$ | 6,945 | 0.763423 | 1.526847 | 0.775106 | 7.717e−3 | 7.778e−3 |
| $10^{6}$–$10^{7}$ | 50,811 | 0.753257 | 1.506514 | 0.761709 | 5.646e−3 | 5.613e−3 |
| $10^{7}$–$10^{8}$ | 381,332 | 0.757884 | 1.515769 | 0.764278 | 4.237e−3 | 4.240e−3 |
| $10^{8}$–$10^{9}$ | 2,984,194 | 0.757546 | 1.515092 | 0.762552 | 3.316e−3 | 3.317e−3 |
| **all** | 3,424,505 | **0.757549 ± 0.000389** | **1.51510 ± 0.00078** | **0.76268** | 3.4245e−3 | 3.4253e−3 |

So $\hat E\cdot2C_2=1.00021$ over the whole chain, and the mass is where the formula says it should be:
$\hat m=0.76268$ against $1/(2C_2)+2/\langle t^2\rangle=0.76258$ — the pair's $2/t^2$ correction, matching
to 0.01%. The density comes out right too: $\rho=3.4245\times10^{-3}$ against $2C_2/\langle t^2\rangle
=3.4253\times10^{-3}$.

**The one exact identity worth having** (`energy_times_density`): with $E$ the mean gap and $\rho$ the
pairs per unit line, $E\cdot\rho=1$ — because $E=\text{span}/m$ and $\rho=m/\text{span}$. Measured:
$1.0000$. It is bookkeeping, not a discovery, and it is the reason the *per-handoff* normalisation is the
one that stays flat.

## 2. Scaling: what changes and what does not

The law is **homogeneous of degree 2 in $t$** (`homogeneous_energy`): multiply $\log p$ by $\lambda$ and

$$\hat E\mapsto\lambda^{2}\hat E,\qquad a\mapsto a\ (\text{scale-free}),\qquad \rho\mapsto\lambda^{-2}\rho
\quad(\texttt{scaled\_degrees}).$$

That is the whole of the "scaled formula" content: **one power of the scale appears, in the energy, and the
acceleration is the invariant.** It is also why a per-segment normalisation drifts (the pair's $2/t^2$
does not scale like $t^2$) while the per-handoff one does not.

## 3. The two conversions, with their constants

Neither is a discovery; each is the same formula in another unit, and the constant is named.

| reading | formula | constant | value at $\langle t^2\rangle=385.5$ |
|---|---|---|---|
| kelvin | $T=\kappa\,t^{2}$ | $\kappa=(1/(2C_2))/3R=0.030364$ K per unit $t^2$ | **11.7 K** |
| joule per mole | $E=3R\kappa\,t^{2}=(1/(2C_2))\,t^{2}$ | same coefficient, $0.75739$ J mol⁻¹ per unit $t^2$ | **292 J/mol** |

and the identity that makes the second column true (`conversion_identity`):

$$3R\,\kappa=\frac{1}{2C_2}\quad\text{exactly},$$

because $\kappa$ was *defined* as $(1/(2C_2))/3R$. So the kelvin and joule readings of the prime formula
carry one and the same coefficient; $\kappa$ only moves the number from $\log^2p$ to kelvin. At
$t=\log10^{12}$ the pair reads 23.2 K and 578 J/mol.

## 4. Mass: what is defined here and what is not

**On the prime side mass is a count or a span.** The pair is 2 units of integer line, the handoff's total
gap is $T=\text{gap}+2$, and "density" is pairs per unit span. Every one of those is exact and none is a
gram.

**On the element side mass is measured**, not derived:

$$M(Z)=2.619\,Z-9.36\ \text{u},\qquad R^2=0.9985,\ \text{rms }3.5\ \text{u},$$

and from it the per-gram heat capacity $c=3R/M$ follows with $r=0.9955$.

**The two are not connected by a mass identification.** The only bridge between the sides is $\kappa$, a
conversion; a count does not become a gram because it is scaled. The record's sharpest statement of this
is `linear_mass_law_blind`: a mass law linear in the count prices every fission split at its intercept
(8.72 GeV for a 200 MeV process). So the mass formula here is honest about its two halves and does not
join them.

## 5. What to use, and what not to

| you want | use | because |
|---|---|---|
| the span of a window of twin starts | $p_N-p_1=(2C_2)^{-1}\sum\log^2p_i$ | exact given the law, 0.022% at $10^9$ |
| the energy per handoff | $\hat E=1/(2C_2)$, or $a/2$ | measured, 0.001% |
| a comparison across scales | the scaled trio, and the homogeneity rule | one power of the scale, in the energy |
| a temperature | $T=\kappa t^2$ — **and say κ** | conversion, not measurement |
| joules | $E=(1/(2C_2))t^2$ J/mol — **and say so** | conversion through $3R$ |
| a mass in grams | **not from this side** | there is no gram in the primes; use $M(Z)$ on the element side |

## 6. Reliability

Every number above is produced by `scripts/prime_scales.py`, which is in `verify-all.sh`. The
coefficient is measured with its standard error ($0.757549\pm0.000389$), the per-decade spread is
$\pm0.6\%$ at the smallest window and $\pm0.006\%$ at the largest, and the two identities
($\hat m$'s correction and $E\cdot\rho=1$) are checked against the same run rather than asserted.
