# The count formulas: base, twin ladder, twin, double twin — and every relation between them

You asked for an explicit formula for the twin count, the base count, the double twin count, and all
relations between them, and for the theorems to be usable. This note gives each of the four counts a
definition, one exact formula, and one measured law, says which of those is which, and lists the ten
relations with their status. It adds one new theorem set
([`count-formulas.lean`](count-formulas.lean), 16 theorems, 0 `sorry`) and two new measurements.

The short answer, before the detail:

* **The base count and the twin-ladder count have a genuine explicit formula with zeros in it**, and
  the zeros belong to $L(s,\chi_{-3})$ — not to $\zeta$. They are **found in the primes** here:
  19 of 19 spectral peaks land on a zero of that $L$-function, 25 of 25 zeros in the window are
  recovered, amplitudes follow $2/\gamma$ to 0.8%.
* **The twin count has no zero-sum formula**, and that is a fact about the object, not a gap in the
  work: the twin indicator has no Euler product, so there is no $L$-function to have zeros. What it
  does have — and this is exact, not asymptotic — is the telescoping identity
  $\sum\text{air} = (\text{last} - \text{first}) - 2\hat N$, i.e.
  **count = span ÷ mean total gap**, with the mean gap the measured law $t^2/(2C_2)$.
* **The double twin count has a formula with no free parameter**, $D(x) \sim (2C_2)^2\mathrm{Li}_3(x)$,
  and it holds to 1–2% over $10^6$–$10^9$.
* A *trend* in the zeros is not a proof of anything about twins, and the zeros' **positions** are RH
  either way. §3 says exactly where the line falls.

## 0. The four counts

| your word | the count | Lean | the exact formula | status |
|---|---|---|---|---|
| **base count** | $B(x)=\#\{p\le x: p=1 \pmod 6\}$ — the $4+6k$ ladder | `Counts.baseCount` | $\psi(x;6,1)-\psi(x;6,5)=-\sum_\rho x^\rho/\rho+O(\log^2 x)$, $\rho$ over $L(s,\chi_{-3})$ | **proved** as arithmetic, **measured** as zeros |
| **twin ladder** | $K(x)=\#\{p\le x: p=5 \pmod 6\}$ — the $5+6k$ ladder | `Counts.ladderCount` | the same formula, one sign flipped | **proved** + **measured** |
| **twin count** | $N(x)=\#\{p\le x: p, p+2 \text{ prime}\}$ | `Counts.twinCount` | no zeros; $\sum\text{air}=\text{span}-2\hat N$ (exact) and $N\sim 2C_2\mathrm{Li}_2$ | **measured**, 0.02% |
| **double twin count** | $D(x)$: handoffs with no prime between the departing partner and the arriving start | `Counts.handoffs` is $\hat N=N-1$ | $D=\#\{\text{consecutive primes } r<s: r-2,\ s+2\ \text{prime}\}$, $D\sim(2C_2)^2\mathrm{Li}_3$ | **measured**, 1–2% |

$C_2=0.6601618$ is the twin constant, $\mathrm{Li}_k(x)=\int_2^x dt/\log^k t$, $2C_2=1.3203236$, and
the counts below $10^9$ are exactly the record's own numbers: $\hat N=3{,}424{,}505$ handoffs,
$D=234{,}287$ merges, air $=4$ exactly $28{,}388$ times.

## 1. Three kinds of "explicit formula", and which count gets which

An explicit formula is a statement of one of three forms. They are not interchangeable, and which
one is available is decided by what the count *is*.

**(a) A zero sum.** If the count is a sum of $\Lambda(n)$ weighted by a *multiplicative* function $f$
that is a Dirichlet character, then $\sum f(n)\Lambda(n)$ has an Euler product, hence an $L$-function,
hence a zero sum by Riemann–von Mangoldt. Primes in a residue class are exactly this case, which is
why the **base count and the twin-ladder count have zero sums**.

**(b) A telescoping identity.** Any count over an *ordered* list is a span divided by a mean step,
with nothing left over. This is exact and needs no analytic input — and it is the whole of what the
twin count has that is exact.

**(c) A singular series.** The density of a fixed pattern of $k$ primes is a Hardy–Littlewood object
$\mathfrak{S}(h)\int dt/\log^k t$: exact as a constant, conjectural as a theorem. Twins, quadruplets
and every merge shape are (c) and only (c).

Twins are not case (a) because $\mathbf{1}_{p,\,p+2}$ is a condition on a *tuple*, not on a residue:
there is no multiplicative weight whose $\Lambda$-sum counts twin starts. That failure is the
sieve's parity obstruction, and it is why the twin count's residual sits *at* the zero bound without
resolving a zero ([`riemann-zeros.md`](riemann-zeros.md) §2). You cannot fix it by finding a better
statistic: there is nothing to expand.

## 2. The base count and the twin ladder: the zeros of $L(s,\chi_{-3})$, found in the primes

$1 \pmod 6$ and $5 \pmod 6$ are the two values of the real, odd character $\chi=\chi_{-3} \pmod 3$ on
the primes. Its Dirichlet series is $L(s,\chi)=3^{-s}\left(\zeta(s,\tfrac13)-\zeta(s,\tfrac23)\right)$,
and with $\Lambda(s,\chi)=(3/\pi)^{(s+1)/2}\Gamma((s+1)/2)L(s,\chi)$ the root number is $1$, so
$\Lambda(s,\chi)=\Lambda(1-s,\chi)$ — real on the critical line, and its sign changes are the zeros.

**The formula (exact).** With $\psi(x;6,a)=\sum_{n\le x,\,n\equiv a(6)}\Lambda(n)$,

$$\psi(x;6,1)-\psi(x;6,5)\;=\;-\sum_{\rho}\frac{x^{\rho}}{\rho}\;+\;O(\log^2 x),\qquad \rho \text{ over the zeros of } L(s,\chi_{-3}),$$

and $\pi(x;6,a)$ follows by partial summation, i.e. with $\mathrm{li}(x^\rho)$ in place of
$x^\rho/\rho$. So **the split of the primes into the two ladders is a zero sum**, and the count on
each ladder is $\mathrm{li}(x)/2$ plus half of it — which is why $B/(\mathrm{li}(x)/2)$ is $0.99993$
at $10^9$.

**The zeros (computed, then confirmed from the primes).** First eight, all on the line:

$$8.039737,\ 11.249206,\ 15.704619,\ 18.261997,\ 20.455771,\ 24.059415,\ 26.577869,\ 28.218165,\ \dots$$

(28 zeros below 70; the full list is written to [`tableV_L_zero_chi3.csv`](tableV_L_zero_chi3.csv).)

**The measurement.** Bin $\psi(x;\chi)$ in $\log x$, divide by $\sqrt x$, transform. On $x\le10^7$
(4000 bins, resolution 0.68) the spectrum has 19 peaks above 8% of the maximum, and:

| quantity | measured |
|---|---|
| peaks landing on a zero of $L(s,\chi_{-3})$ | **19 of 19** (tolerance 0.82 = 1.2 resolution elements) |
| zeros in the window recovered | **25 of 25** |
| amplitude against the $2/\gamma$ law | **1.008** mean, spread 0.880–1.197 |
| spectral power within 0.82 of a zero | **0.955** (shuffle: $0.684 \pm 0.050$) |

The signal is not "a peak near a zero" — it puts 95.5% of the window's power on the zeros' frequencies
where a shuffle puts 68%, and the amplitudes follow $2/\gamma$, the same law the Riemann zeros obey
([`zeros-in-the-primes.md`](zeros-in-the-primes.md)). That is the *first* explicit formula in the
record with a visible zero spectrum of its own, and it is a different $L$-function from $\zeta$.

**What it settles about the base count.** $B$ and $K$ are not two independent counts: by
[`count-formulas.lean`](count-formulas.lean) `primeCount_partition`, $P=B+K+2$ exactly, so the pair
is one question. Their difference is the character sum, and it oscillates at the zeros above. Measured
$B-K$: $-6$ at $10^3$, $-34$ at $10^6$, $-419$ at $10^8$, $-2106$ at $10^9$ — the $5+6k$ ladder
carries the excess, and $\sqrt x=31{,}623$ at $10^9$, so the excess is $7\%$ of $\sqrt x$: the
Chebyshev bias of this character, at the size the theory allows.

## 3. The twin count: what it has, and where the zeros stop

**Exact (proved).** For twin starts $p_0<p_1<\dots<p_n\le x$, with $\text{air}_i=p_{i+1}-p_i-2$,

$$\sum_{i<n}\text{air}_i \;=\; (p_n-p_0)\;-\;2n \qquad\text{(Lean: \texttt{air\_sum\_identity}, \texttt{count\_from\_span})}$$

so $n = \big((p_n-p_0)-\sum\text{air}\big)/2$: **the count is the span divided by the mean total gap**,
with no free parameter once the mean is known. Verified exactly in the scan: the sum of the total gaps
equals $\text{last}-\text{first}$ to the digit, $999{,}999{,}188$ at $10^9$, and
$\sum\text{air}=999{,}999{,}188-2\cdot3{,}424{,}505=993{,}150{,}178$.

**Measured.** $\langle\text{gap}\rangle=t^2/(2C_2)$, so $N(x)=2C_2\,\mathrm{Li}_2(x)$:

| $x$ | $N(x)$ | $N/\mathrm{HL}_2$ |
|---|---|---|
| $10^6$ | 8,169 | 0.99042 |
| $10^7$ | 58,980 | 1.00385 |
| $10^8$ | 440,312 | 0.99987 |
| $10^9$ | 3,424,506 | 0.99977 |

**Where the zeros stop — and this is the honest answer to "a trend in the zeta that correlates to the
twin gaps".** The twin count is a Hardy–Littlewood object. It responds to the *same* prime-counting
function that carries the zeros (both are made of primes), so a coarse trend in a twin statistic will
correlate with a coarse trend in $\psi(x)-x$; but that correlation comes from the shared $\psi$, not
from a twin analogue of von Mangoldt's formula, and a twin analogue does not exist. A trend is not a
proof in two separate ways:

1. **There is no identity to prove.** A proof of an oscillation needs a functional equation and an
   Euler product; the twin indicator has neither. Anything stated as "the twin count oscillates at
   $\gamma$" would be a conjecture about a correlation, and correlations computed over a finite range
   are measurements — which is what §3's table is.
2. **Even with the identity, the zeros' positions would still be open.** The explicit formula gives the
   zeros' *amplitudes and frequencies*, not their locations; the locations are the Riemann hypothesis,
   and no counting formula decides it. The record already says this in (L2) of the master theorem.

What *would* be new is a twin-side spectral peak that survives a control which randomises the twin
subset inside the same primality — and the record tried that and did not find one
([`riemann-zeros.md`](riemann-zeros.md) §2: the residual sits at the zero bound without resolving a
zero). The zeros found in §2 above are a different object and they are real: they belong to
$\chi_{-3}$, and they are in the *base* count, not in the twin count.

## 4. The double twin count

**Definition (exact).** A merge is a handoff with no prime between the departing partner $p+2$ and the
arriving start $q$, i.e. $p+2$ and $q$ are **consecutive primes**. So

$$D(x)=\#\{\text{consecutive primes } r<s,\ s\le x:\ r-2 \text{ prime and } s+2 \text{ prime}\},$$

a condition on two consecutive primes at once — no character, no zero sum.

**The residue lock (proved).**

* air $\equiv 4 \pmod 6$ (Lean: `air_mod_six`), so air $=4+6k$ (`air_is_four_plus_six`) and the total
  $T=\text{air}+4\equiv2\pmod 6$ (`total_mod_six`) — the two alphabets of the record;
* the minimal merge, air $=4$, is the quadruplet $p,p+2,p+6,p+8$, and it can only start at
  $p\equiv 11 \pmod{30}$ (Lean: `quadruplet_start_mod_30`) — the three twin types $11,17,29$ mod 30
  (Lean: `twin_start_mod_30`), of which $17$ sends $p+8$ and $29$ sends $p+6$ to a multiple of five.

**The decomposition.** $D=\sum_{k\ge0}\#\{$air $=4+6k\}$, each term a four-prime pattern
$\{0,2,6+6k,8+6k\}$ with its own singular series. Measured class shares at $10^9$, over 3,424,504
handoffs (air $\bmod 30$):

| class | 28 | 10 | 16 | 4 | 22 |
|---|---|---|---|---|---|
| share at $10^9$ | **31.2%** | 23.6% | 22.1% | 11.9% | 11.1% |
| the record's sheet at $10^8$ | 30.7% | 24.0% | 22.1% | 12.1% | 11.1% |

and the individual small airs: air $=4$ exactly 28,388 times (**the record's quadruplet count, to the
digit**), air $=10$ 75,478, air $=16$ 55,399, air $=22$ 34,959, air $=28$ 108,563.

**The law (no free parameter).** A merge is "the next prime after a pair happens to start a twin", at
the measured rate $2C_2/\log p$, so $D\sim(2C_2)^2\mathrm{Li}_3(x)=(1.32032)^2\mathrm{Li}_3(x)$:

| $x$ | $D(x)$ | $D/\mathrm{HL}_3$ | $D/\hat N$ | $2C_2/\log x$ |
|---|---|---|---|---|
| $10^6$ | 863 | 0.978 | 0.1057 | 0.0957 |
| $10^7$ | 5,274 | 1.007 | 0.0894 | 0.0819 |
| $10^8$ | 34,380 | 1.016 | 0.0781 | 0.0717 |
| $10^9$ | 234,287 | 1.011 | 0.0684 | 0.0637 |

$1$–$2\%$ over three decades: a real formula at the few-percent level, not at the twin count's
$0.02\%$. The cumulative $D/\hat N$ runs $7\%$ above $2C_2/\log x$ at $10^9$ because the *decade* rate
is the one that matches (the record measured $p_{\rm merge}\langle t\rangle=1.327\pm0.016$ against
$2C_2=1.32032$, five decades, $+0.5\%\pm1.2\%$).

**Measured, and not predicted: merges cluster.** Segments of exactly $k$ pairs against a geometric
model $\hat N p^{k-1}(1-p)^2$ at $p=2C_2/\log 10^9$:

| $k$ pairs | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| measured | 2,971,977 | 203,254 | 13,981 | 956 | 47 |
| geometric | 3,002,041 | 191,266 | 12,186 | 776 | 49 |
| ratio | 0.99 | **1.06** | **1.15** | **1.23** | 0.95 |

A merge raises the chance of the next merge by $6\%$, and of the second by $15\%$: the merge indicator
is *not* independent, which is the quantitative form of the record's "16,046 adjacent merges against
13,982 three-pair segments". (The $k=1$ counting and the $k\ge5$ tail are the same run census as
[`merge-and-the-count.md`](merge-and-the-count.md); the segments total $3{,}190{,}218$ here against
$H-D+1=3{,}190{,}219$ there, a one-segment difference in how the bottom pair $(3,5),(5,7)$ is seated.)

## 5. All the relations, with status

| # | relation | use it for | status |
|---|---|---|---|
| R18 | $P(x)=B(x)+K(x)+2$ | the two ladders are one count; $2$ and $3$ are the only primes off both | **proved** (`primeCount_partition`) |
| R19 | twin start $>3$ $\Rightarrow p\equiv5\ (6)$ | the twin count is a subcount of one ladder: $N\le K+1$ | **proved** (`twin_start_mod_six`, `twin_le_ladder`) |
| R20 | twin start $>5$ $\Rightarrow p\equiv11,17,29\ (30)$ | the twin key's three pair types $13,79,91$ | **proved** (`twin_start_mod_30`) |
| R21 | air $\equiv4\ (6)$, $T=\text{air}+4\equiv2\ (6)$ | which alphabet a gap is in | **proved** (`air_mod_six`, `total_mod_six`) |
| R22 | quadruplet $\Rightarrow p\equiv11\ (30)$ | the minimal merge's class | **proved** (`quadruplet_start_mod_30`) |
| R23 | $\sum\text{air}=\text{span}-2\hat N$ | count = span ÷ mean gap; catch a slip | **proved** (`air_sum_identity`) |
| R24 | $B-K=\psi(x;6,1)-\psi(x;6,5)=-\sum_\rho x^\rho/\rho$ | the split as a zero sum | **proved** as a formula, **measured** as a spectrum |
| R25 | $N(x)=2C_2\mathrm{Li}_2(x)$ | the twin count | **measured**, 0.02% |
| R26 | $D(x)=(2C_2)^2\mathrm{Li}_3(x)$ | the double twin count | **measured**, 1–2% |
| R27 | $D/\hat N=2C_2/\log x$ | the merge rate, no parameter | **measured**, decade-wise 0.5% |
| R28 | segments $=\hat N-D+1$; sizes cluster $\times1.06,\ \times1.15,\ \times1.23$ | how the pairs group | **measured** |

R18–R23 are theorems in [`count-formulas.lean`](count-formulas.lean); R24's analysis is measured in
`scripts/base_key_zeros.py`; R25–R28 are `scripts/count_formulas.py`. All eleven are re-asked on
random inputs in [`random-counts.md`](random-counts.md): 16,050 draws, 0 failures, and no constant
drifts across four decades.

## 6. The measurements, and the cross-checks

`python3 scripts/count_formulas.py 1e9` (4.7 s), exact at every step:

| $x$ | $P$ | $B$ | $K$ | $N$ | $\hat N$ | $D$ | $D/\hat N$ |
|---|---|---|---|---|---|---|---|
| $10^3$ | 168 | 80 | 86 | 35 | 34 | 9 | 0.2647 |
| $10^5$ | 9,592 | 4,784 | 4,806 | 1,224 | 1,223 | 162 | 0.1325 |
| $10^7$ | 664,579 | 332,194 | 332,383 | 58,980 | 58,979 | 5,274 | 0.0894 |
| $10^8$ | 5,761,455 | 2,880,517 | 2,880,936 | 440,312 | 440,311 | 34,380 | 0.0781 |
| $10^9$ | 50,847,534 | 25,422,713 | 25,424,819 | 3,424,506 | 3,424,505 | 234,287 | 0.0684 |

The full table with the Hardy–Littlewood columns is [`tableU_count_formulas.csv`](tableU_count_formulas.csv).
Checks that ran, all exact:

* $\pi(10^9)=50{,}847{,}534$ — the known value, and the scan's independent prime counter agrees with
  $2+B+K$ to the digit;
* the segmented scan against a plain full sieve at $10^6$: **agrees on all six counts**;
* $\sum$ total gaps $=$ last $-$ first at every decade; $\sum$ air $=$ span $-2\hat N$;
* air $\bmod 6\in\{0,4\}$ over 3.4M handoffs, the single $0$ being the pair $(3,5)$;
* air $=4$ at $10^9$: 28,388 — the record's quadruplet count;
* the air class shares at $10^9$ against the record's $10^8$ sheet: agreement to $0.5$ points.

## 7. How to use it

The Lean file is an API; every name below is `Counts.`-prefixed and takes the bound as its last
argument.

```lean
import Mathlib
-- results/count-formulas.lean, namespace Counts
#check @Counts.prime_mod_six          -- p prime, 3 < p → p % 6 = 1 ∨ p % 6 = 5
#check @Counts.twin_start_mod_six     -- twin start > 3 → p % 6 = 5
#check @Counts.twin_start_mod_30      -- twin start > 5 → p % 30 ∈ {11,17,29}
#check @Counts.air_mod_six            -- (q - p - 2) % 6 = 4
#check @Counts.air_is_four_plus_six   -- ∃ k, air = 4 + 6k
#check @Counts.total_mod_six          -- (q + 2 - p) % 6 = 2
#check @Counts.quadruplet_start_mod_30 -- p,p+2,p+6,p+8 prime, p > 5 → p % 30 = 11
#check @Counts.primeCount_partition   -- primesUpTo n = base + ladder + 2  (n ≥ 3)
#check @Counts.twin_le_ladder         -- twinCount n ≤ ladderCount n + 1
#check @Counts.air_sum_identity       -- Σ (p(i+1) - p i - 2) = p n - p 0 - 2n
#check @Counts.count_from_span        -- the same solved for the span
#check @Counts.counts_100             -- B=11, K=12, N=8, P=25, evaluated
```

The definitions are computable (`baseCount`, `ladderCount`, `twinStarts`, `twinCount`, `handoffs`), so
`decide` runs them on any bound small enough for the kernel; above $\sim10^3$ use the sieve.

| you want | run |
|---|---|
| the four counts, the laws, the ratios, the segment census | `python3 scripts/count_formulas.py 1e9` |
| the base count's zeros, from the primes | `python3 scripts/base_key_zeros.py 1e7 1e3 4000` |
| the proofs | `lean results/count-formulas.lean` |
| random tests of every relation | `python3 scripts/random_count_relations.py 2000 1e9` |
| everything | `bash scripts/verify-all.sh` |

## 8. What this does not say

* **It does not put zeros in the twin count.** The twin and double-twin formulas are singular-series
  laws, measured; the base and twin-ladder formulas are zero sums, proved in form and measured in
  spectrum. Mixing the two would be the error this note exists to prevent.
* **It does not say where the zeros are.** The enumeration finds sign changes of $\Lambda(s,\chi_{-3})$
  *on* the critical line, at the spacings the density predicts, down to 70 — it does not prove there
  are no zeros off it. What is proved is the structure that forces a *symmetric* zero onto the line
  ($\Lambda(s)=\Lambda(1-s)$ real on it, the master theorem's (L1) in the other case); the analogue of
  RH for this $L$-function is as open as RH.
* **The Hardy–Littlewood constants are taken, not derived.** $2C_2$ and $(2C_2)^2$ are the record's
  measured constants; the tuple densities are conjectures as theorems and measurements here.
* **$D$'s law is 1–2%, and its residual is not monotone** — unlike the twin count's 0.02%. The
  difference is real: a merge is a two-prime condition (correlated), a twin is a one-prime condition
  on a shifted pair.
