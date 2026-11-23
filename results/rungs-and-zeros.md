# The rungs and the Riemann zeros

## First: two different orderings, and my wording was ambiguous

| class | value $V$ | measured mean air at $10^{10}$ | share of handoffs |
|---|---|---|---|
| 32 | 2.0 | **377.9** (largest) | 10.39% |
| 14 | 3.5 | **345.9** (smallest) | 11.82% |
| 26 | 5.0 | 357.7 | 11.14% |
| 8 | 6.5 | 352.0 | 11.90% |
| 20 | 8.0 | 367.5 | 11.07% |

Your ladder order is $32<14<26<8<20$. The measured-air order is $14<8<26<20<32$ — nearly reversed.
So: the **bottom rung of your ladder is class 32**, and class 32 has the **largest** air. When I said
"lowest rung is class 14" I was ordering by measured air, not by your value ladder. Apologies.

Mechanism: air falls as a handoff gets more frequent. Class 14 is the 79→91 and 91→13 handoffs, two of
the three commonest, so it has the shortest air; class 32 is the three self-handoffs, the rarest, so it
waits longest.

## Do the rungs sit at the zero ordinates? No.

Nearest ζ-zero to each rung:

| rung | 8 | 14 | 20 | 26 | 32 |
|---|---|---|---|---|---|
| nearest zero | 14.1347 | **14.1347** | 21.0220 | 25.0109 | 32.9351 |
| distance | 6.13 | **0.135** | 1.02 | 0.99 | 0.94 |

Mean nearest distance 1.84 against a null median of 3.13, lower-tail $p=0.19$ over 20,000 random rung
sets — suggestive, not significant. The single real hit is $14\to14.1347$. The base floors are entirely
typical ($p=0.70$).

And a dimensional point that settles it: **your whole value ladder ($2$ to $9.5$) lies below the first
zero at $14.1347$.** There are no ζ zeros in the ladder's window at all, so the ladder cannot be a set of
zero ordinates.

## The correct spectrum for a mod-30 object

ζ knows nothing about mod 30. The mod-30 structure's spectrum is the set of zeros of the eight
Dirichlet $L$-functions mod 30 — five distinct $L$-functions, conductors 1, 3, 5, 15:

| spectrum | conductor | first zeros |
|---|---|---|
| $\zeta$ (principal) | 1 | 14.1347, 21.0220, 25.0109, 30.4249, 32.9351 |
| $\chi_{-3}$ | 3 | 8.0397, 11.2492, 15.7046, 18.2620, 20.4558 |
| $\chi_{5}$ | 5 | 6.6485, 9.8314, 11.9589, 16.0338, 17.5670 |
| $\psi$ (quartic, mod 5) | 5 | 6.1836, 8.4572, 12.6750, 14.8250, 17.3378 |
| $\chi_{-15}$ | 15 | 3.0570, 5.3432, 7.2676, 10.1338, 12.1597 |
| $\psi\chi_{-3}$ (complex, mod 15) | 15 | 2.7346, 5.2430, 8.4147, 10.1876 |

Computed by Hurwitz-zeta representation $L(s,\chi)=q^{-s}\sum_a\chi(a)\zeta(s,a/q)$ and root-finding on
the critical line; each zero verified to $|L|<10^{-8}$.

**Against this spectrum the rungs are still not privileged**: 58 zeros in $[1,36]$ (density 1.66 per
unit, mean spacing 0.60), so *every* integer finds a zero within about 0.2. Twin floors: mean nearest
distance 0.30, null median 0.23, $p=0.77$. Base floors: 0.26, $p=0.64$. The $8.04$-vs-$8$ hit is worth
0.83 expected hits by chance. Matching rungs to zero heights cannot confirm or refute anything here.

## What the zeros actually do with the rungs: they are the rungs' resonances

The explicit formula, read off the eight residue classes mod 30. For each character,
$F_\chi(u)=e^{-u/2}\psi(e^u;30,\chi)$ with $u=\log x$, Fourier-analysed over primes below $10^{10}$:

| spectrum | predicted zeros | measured peaks | peak / background |
|---|---|---|---|
| $\zeta$ | 14.1347, 21.0220, 25.0109, 30.4249, 32.9351 | 14.14, 21.04, 25.02, 30.44, 32.93 | 60, 40, 34, 28, 26 |
| $\chi_{-3}$ | 8.0397, 11.2492, 15.7046, 18.2620, 20.4558 | 8.05, 11.27, 15.72, 18.26, 20.47 | 78, 56, 40, 34, 31 |
| $\chi_{5}$ | 6.6485, 9.8314, 11.9589, 16.0338, 17.5670 | 6.66, 9.83, 11.94, 16.01, 17.54 | 75, 51, 42, 31, 29 |
| quartic | 6.1836, 8.4572, 12.6750, 14.8250, 17.3378 | 6.18, 8.44, 12.66, 14.81, 17.35 | 80, 58, 39, 33, 29 |
| $\chi_{-15}$ | 3.0570, 5.3432, 7.2676, 10.1338, 12.1597 | 3.07, 5.32, 7.29, 10.11, 12.18 | 48, 28, 20, 15, 12 |
| $\psi\chi_{-3}$ | 2.7346, 5.2430, 8.4147, 10.1876, 11.9074 | 2.73, 5.23, 8.44, 10.21, 11.89 | 55, 29, 18, 15, 13 |

Every predicted zero is a measured peak, positions agreeing to about 0.05, standing 12–80 times above
the local background. So the rungs do not *sit at* the zeros — the rung counts *ring* at them.

The reason, exactly: for $(a,30)=1$,
$$\psi(x;30,a)=\frac18\sum_{\chi \bmod 30}\overline{\chi(a)}\,\psi(x,\chi).$$
Every character enters every rung with weight $\overline{\chi(a)}/8$ — **modulus $1/8$, identical for
all eight slots**, differing only in phase. So:

* all five rungs hear **the same frequencies** (the same zeros);
* they differ only by a phase rotation, which cannot change a magnitude;
* and that is *why* the three twin classes are equidistributed — measured $1:1.0001:1.0000$ at $10^{10}$.

Measured consistency: the three twin rungs' spectra (residues 11, 17, 29) correlate 0.73–0.86 and share
peak positions at low $\gamma$; mean amplitudes 52.7, 59.2, 58.8 — equal to 11%, as the phase argument
requires.

So the rungs appear in the zero-world twice, neither time as heights:

1. as **phases/weights** $\overline{\chi(a)}/8$ on shared frequencies (the line above);
2. as **constants** in the singular series: $2C_2=\prod_p f_p$ with $f_3=\tfrac34$ and $f_5=\tfrac{15}{16}$,
   so the wheel supplies $2C_2 = \tfrac34\cdot\tfrac{15}{16}\cdot 1.8778$. Your $3/4$ reducer *is* the
   factor-3 local density for the twin pattern.

## Caveats I am not going to paper over

* The low-$\gamma$ region is contaminated. The principal spectrum shows a spurious peak at 2.68, and the
  individual rung spectra share a peak at 4.27 that is a zero of **none** of the five mod-30
  $L$-functions (checked: in $[3.5,8]$ the spectra have zeros only at 5.243, 5.343, 6.184, 6.649,
  7.268). Both are finite-range artefacts, and both sit below $\gamma\approx5$.
* The per-rung spectra contain peaks above $\gamma\approx10$ that I have not identified, because I
  computed only the first five or six zeros of each spectrum.
* Extending to $10^{11}$ would sharpen every peak by a factor 1.1 and push the artefact down; that is
  a twenty-minute run.
