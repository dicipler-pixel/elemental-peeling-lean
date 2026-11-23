# The zeta zeros in the master theorem: forced, fluctuating, out of reach

> **Update — L2 is now a measurement, not a limit.** The follow-up run
> [`zeros-in-the-primes.md`](zeros-in-the-primes.md) resolves `(\psi(x)-x)/\sqrt x` by frequency and
> recovers **twelve Riemann zeros** from the primes below $10^7$, with the $2/\gamma$ amplitudes and a
> shuffled control. The "out of reach" verdict below still stands for the *twin* count, which is what this
> note was about, and which is a different object (§2's residual table is unchanged).

There are three honest things to say, and they are different in kind. The trivial zeros are **forced** and
say nothing about arithmetic. The non-trivial zeros are **the remainder terms** of every counting law —
which is exactly where this record's residuals live. And the record's one genuinely zero-adjacent
measurement turns out to be the *other* bias, whose main term is **not** zeros. No coincidence is claimed
anywhere below; where two numbers sit within an order of magnitude of each other, I say so and leave it.

## 1. The trivial zeros are the forced lattice

$$\zeta(-2n)=0,\qquad n=1,2,3,\dots$$

They come from the Gamma factor in the functional equation and carry no arithmetic information — every
counting law is correct to leading order whether or not you think about them. In the table, the forced
part is the closure ladder: capacities are even, and the lattice is $2n^2$ (proved: `trivial_zeros_even`,
`trivial_zeros_negative`, `capacity_even`, `coulomb_cumulant`).

So the correspondence is:

> **the trivial zeros are to $\zeta$ what the closure ladder is to this table** — the part fixed by the
> symmetry rather than by the primes, and the part that is true of everything and explains nothing.

That is all there is. The trivial zeros are not a hidden coordinate of the table, and the fact that both
lattices are even is a fact about the number 2, not a bridge.

## 2. The non-trivial zeros are the remainders — and the record already sits at their scale

$$\rho=\tfrac12+i\gamma,\qquad \gamma_1=14.1347,\ 21.022,\ 25.0109,\ 30.4249,\ 32.9351,\dots$$

The functional equation's symmetry $s\mapsto1-s$ fixes the critical line (proved: `critical_line_fixed`),
so any self-conjugate zero has real part exactly $1/2$. Beyond that, what the zeros *do* is supply the
remainder: Schoenfeld's explicit bound is

$$|\psi(x)-x|\le\frac{\sqrt x\,\log^2x}{8\pi}\qquad (x\ge 74),$$

and every one of this record's counting laws has a residual of that size. The twin count is the case in
hand: the parameter-free formula is $N_2(x)=2C_2\int_2^x dt/\log^2t$, and its measured residual is

| $x$ | $10^8$ | $10^9$ | $10^{10}$ | $10^{11}$ | $10^{12}$ |
|---|---|---|---|---|---|
| residual | $+0.013\%$ | $+0.023\%$ | $-0.005\%$ | $-0.003\%$ | $-0.0014\%$ |
| zero bound $\log^2x/8\pi\sqrt x$ | $0.135\%$ | $0.054\%$ | $0.021\%$ | $0.0081\%$ | $0.0030\%$ |

The residual and the bound are **within a factor of ten of each other at every scale — above it at
$10^9$, below it at the rest** — and the residual is not visibly oscillatory in the way a zero's
contribution would be. The correct statement is therefore narrow:

> **the record has reached the scale at which a zero could first show up, and has not resolved one.**

To see one you would need the twin count to better than $10^{-5}$ relative at $10^{18}$-ish, or the
oscillation isolated by a spectral analysis of the residual — neither is a matter of more of the same
sieve.

## 3. The wheel is the finite Euler product, and the zeros are what is left

$30=2\cdot3\cdot5$ with $\varphi(30)=8$ classes (proved: `wheel_is_euler`, `wheel_has_eight_classes`). The
record's exact part — the eight classes, the five air classes, the 16 base cells, 0 exceptions in 224
million handoffs — is the Euler product over the *three smallest primes*. The zeros are the infinite
remainder of that product. In frequency terms the two are far apart:

| object | period in $\log x$ |
|---|---|
| the 30-wheel | 30 |
| $\gamma_1=14.13$ | 0.44 |
| $\gamma_5=32.94$ | 0.19 |

so the wheel is the *DC term* — the lowest possible frequency — and the zeros are the high-frequency
structure above it. That is why the wheel has 0 exceptions and the zeros have never been seen here: they
are two different bands.

## 4. The one place the record *did* measure a prime bias — and its main term is not zeros

Measured on the end digits of consecutive primes (16 cells): the diagonal is suppressed,
$P(\text{same digit})=0.147$–$0.164$ at $2\times10^6$ against $0.25$, rising to $0.186$ at $10^9$ — the
$1/\log p$ decay tabulated below. That is the Lemke Oliver–Soundararajan
bias. Two things must be said about it, and the second corrects the natural guess:

* **It decays as $1/\log x$** — measured over seven decades:

| decade | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|
| $0.25-P(\text{same})$ | 0.129 | 0.108 | 0.095 | 0.086 | 0.077 | 0.070 | 0.064 |
| $\times\log p$ | 1.04 | 1.12 | 1.20 | 1.28 | 1.33 | 1.37 | **1.40** |

so the bias is $c/\log p$ with $c$ converging to about 1.4 — still drifting upward at $10^9$.

* **Its main term is the prime-tuple singular series, not the zeros.** The zeros of Dirichlet $L$-functions
  explain the *single-prime* Chebyshev bias; the consecutive-prime bias is a different and stronger effect,
  produced by the singular series for the tuples, with the zeros entering only its remainder
  (Lemke Oliver–Soundararajan, arXiv:1603.03720; the distinction is drawn clearly in Tao's 2016 note).
  So the record's measured bias is a **Hardy–Littlewood** object — the same $C_2$-family it already uses —
  and not a zeta-zero object.

This matters for the theorem: the temptation is to read any prime-side asymmetry as zero-driven. The
measured asymmetry is not; the zeros are one order below it.

## 5. What goes into the theorem, and with what status

> **(L) The zeta zeros.**
> **(L1)** The trivial zeros are the forced lattice: negative even integers, no arithmetic content —
> the same status as the closure ladder, which is forced by $2n^2$ (proved).
> **(L2)** The non-trivial zeros are the remainder terms: the critical line is the fixed set of
> $s\mapsto1-s$ (proved), and every counting residual in this record lies 3–10× below Schoenfeld's
> unconditional zero bound — at the threshold of resolution and not past it (measured).
> **(L3)** The exact part of the table is the finite Euler product: $30=2\cdot3\cdot5$, eight classes,
> 0 exceptions; the zeros are the infinite remainder, some seventy times higher in frequency
> (proved / measured).
> **(L4)** The one measured prime bias (end digits, diagonal suppressed to 0.15–0.16) is
> $c/\log p$ with $c\to1.4$; its main term is the tuple singular series, not the zeros (measured,
> literature-confirmed).

**What this does not say.** It does not say the zeros are "in" the table, that any of the record's
constants is a zero, or that $\gamma_1$ appears anywhere in its arithmetic. The correlations that survive
are structural and one-directional: the zeros own the remainders, the wheel owns the exact part, and the
record's data stop one order of magnitude short of the zeros' band.

## 6. What would settle more

1. **The residual's spectrum.** Take the twin-count residual $N_2(x)-2C_2\int dt/\log^2t$ at, say, 500
   values of $x$ up to $10^{12}$ and look for the frequencies $2\pi/\gamma_k$ — the periods 0.44, 0.30,
   0.25 in $\log x$. If a peak appears at 0.44, that is a zero seen in the record's own data. (The sieve
   already produces the counts; the residual is 1e-4, so this needs care with the main term's own
   $1/\log$ correction, which is the real obstacle.)
2. **The bias's remainder.** Same analysis on the $1/\log p$ bias — the L-O-S remainder is the sum over
   $L$-function zeros, so its residual is where they live.
3. **Nothing on the trivial zeros.** They are the forced part; there is no experiment to do.
