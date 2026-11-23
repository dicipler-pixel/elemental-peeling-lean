# Inside the segment: what the end digits and the subset-number sequence correlate with — and what causes what

The object: between consecutive twin pairs $(p,p+2)$ and $(q,q+2)$ there are 13.8 primes on average,
47.4M gaps in total below $10^9$, 3,424,503 segments. Two features of the inside are usually named:
the **end digits of the gaps** ($g \bmod 10 \in \{0,2,4,6,8\}$) and the **subset-number sequence**
$k_r = \lfloor r/30 \rfloor$ of the inner primes. Below, everything is either *forced* (a consequence of
the endpoints, with no exceptions), *measured* (a number with a null), or *nothing*.

## 0. First, a tautology that changes how the question is asked

$$\text{class} \;=\;(q+2-p)\bmod 30 \;=\;(\text{air}+4)\bmod 30 .$$

The class is not an independent variable; it **is** the air's residue mod 30. So "does the class cause
the inside?" is exactly "does the air's residue cause the inside?", and the air is fixed by the two
endpoints. Any correlation between the class and an interior quantity must therefore come through the
endpoints' residues or through the length. There is no third route, and the measurements below respect
that.

## 1. Forced: the endpoints forbid one gap digit each

A twin pair ends at $E=p+2$ and the pair types are $11\to13$, $17\to19$, $29\to31$, so

$$E \equiv 13,\ 19,\ 1 \pmod{30}\quad\text{respectively.}$$

The next prime after $E$ must land on an admissible residue, so a gap that carries $E$ onto a multiple
of 5 is impossible:

| pair type | $E \bmod 30$ | one gap digit is impossible | why |
|---|---|---|---|
| $11\to13$ | 13 | **2** | $13+2\equiv15$, $+12\equiv25$, $+22\equiv5$ |
| $17\to19$ | 19 | **6** | $19+6\equiv25$, $+16\equiv5$ |
| $29\to31$ | 1 | **4** | $1+4\equiv5$, $+14\equiv15$, $+24\equiv25$ |

The class fixes which pair types are possible: of the nine type pairs, class 8 is $11\to17$ alone and
class 26 is $17\to11$ alone, while classes 2, 14, 20 are mixtures of three, two and two types. Hence
**two of the five classes can never show one digit in their first gap** — and they don't, in 3.4M
segments:

| class | 0 | 2 | 4 | 6 | 8 |
|---|---|---|---|---|---|
| 2 (mixed, 3 types) | 214,478 | 201,788 | 208,693 | 219,067 | 223,664 |
| **8 (type $11\to17$)** | 83,838 | **0** | 144,259 | 112,331 | 66,956 |
| 14 (mixed, 2 types) | 232,858 | 203,265 | 118,781 | 123,605 | 131,128 |
| 20 (mixed, 2 types) | 156,094 | 105,845 | 106,179 | 268,661 | 121,372 |
| **26 (type $17\to11$)** | 79,603 | 124,990 | 110,611 | **0** | 66,436 |

The same table at the other end (last gap before $q$) is the mirror image, with the same two zeros.
This is the whole of the "class predicts the end digits" effect: mutual information
$0.1186$ bits, of which $0.083$ is the two forced zeros and $0.036$ is what remains among the three mixed classes
(sub-mixture proportions plus the sum constraint of §2).

## 2. Forced: the sum, and the absence of twins inside

$$\sum_{\text{inside}} g \;=\; \text{air},\qquad \sum g \bmod 10 \;=\;\text{class}-4 \pmod{10},$$

and **no gap inside a segment equals 2** — a 2-gap is a twin pair, and the segment is bounded by
consecutive ones. So every interior gap is $\ge 4$ and is $\equiv 0$ or $4 \pmod 6$. That is why the
interior's digit shares differ from the global ones: digit 2 drops from 23.0% (global) to 17.3%
(interior), because all 3.4M twin gaps have been removed by construction.

## 3. A theorem the carry rule was pointing at

Primes above 3 are $\equiv \pm1 \pmod 6$, and a gap of $g\equiv2$ takes $5\to1$, $g\equiv4$ takes
$1\to5$, $g\equiv0$ stays. The residue therefore *alternates* whenever the gap is not $0 \bmod 6$, so the
numbers of $5\to1$ and $1\to5$ steps differ by at most one:

$$\big|N(g\equiv 2) - N(g\equiv 4)\big| \le 1 \quad\text{in any initial segment, always.}$$

Check: below $10^9$ both are **14,107,248** — equal to the unit; below $10^8$ they differ by 1. The
"carry" (a gap $\equiv2 \pmod 6$ cannot be followed by another) is the local form of the same
statement, and it holds inside every segment: 0 violations in 3.4M opportunities.

## 4. Measured: the inside does not know the class

Interior gap digits, first and last removed, by class:

| class | gaps | 0 | 2 | 4 | 6 | 8 |
|---|---|---|---|---|---|---|
| 2 | 13,347,429 | .1885 | .1725 | .2151 | .2390 | .1850 |
| 8 | 4,635,873 | .1886 | .1753 | .2096 | .2367 | .1898 |
| 14 | 8,981,317 | .1806 | .1724 | .2155 | .2423 | .1891 |
| 20 | 9,154,951 | .1889 | .1723 | .2173 | .2344 | .1872 |
| 26 | 4,454,405 | .1890 | .1679 | .2106 | .2402 | .1923 |

All within 1% relative of each other: **the interior does not predict the class.** What it is instead is
the twin-free prime process — its digits are the ambient distribution with the 2-gaps taken out.

The arrow runs one way only, and §4a measures the other one: the *total* gap grades the interior
strongly. Reading "the interior is class-blind" as "the big jump carries nothing" was wrong.

## 4a. The other arrow: what the total gap *does* determine

Four graded dependencies, all monotone in the total and none of them small:

| what the total fixes | measured |
|---|---|
| the count of inner primes | $n=1.599+0.04568\,\text{air}$, $R^2=0.953$ |
| the gap-digit mix | air 4–30: $.245$ $.156$ $.228$ $.243$ $.130$ for digits 0,2,4,6,8; air 1200+: $.185$ $.172$ $.214$ $.240$ $.188$ |
| the mean interior gap | 11.7 at air 4–30 rising to 19.5 at air 1200+ |
| the reuse of 30-blocks (subset numbers) | $0.732 \to 0.595 \to 0.546 \to 0.502 \to 0.477 \to 0.463 \to 0.454$ across the air bins |
| the endpoint digits | forced: first by the start type, last by the end type; $\sum$ digits $\equiv$ air mod 10 |
| the sum itself | $\sum$ gaps $=$ air, 1 exception in 440,309 (the last segment, a boundary artefact) |

And the sum constraint is visible as a compression of the composition. At fixed length $n$ and a narrow
air band, the within-segment spread of the gaps is below what independent draws with the same mean give,
by the finite-sum factor $\sqrt{1-1/(n-1)}$:

| $n$ | air band | mean gap | within-segment sd | independent expectation | ratio |
|---|---|---|---|---|---|
| 6 | 100–106 | 16.7 | 10.4 | 12.5 | 0.83 |
| 6 | 136–142 | 22.7 | 15.5 | 17.0 | 0.91 |
| 10 | 190–196 | 19.0 | 13.3 | 14.3 | 0.93 |
| 20 | 400–406 | 20.0 | 14.8 | 15.0 | 0.99 |

$\sqrt{1-1/(n-1)}$ predicts 0.89, 0.89, 0.94, 0.97 — the shape is right, the first row overshoots.

So the correct statement of the asymmetry: **the total determines the aggregate exactly (the sum), the
count strongly ($R^2=0.95$), the digit mix and block reuse monotonically — while the interior determines
nothing about the class.** One-way information, which is what an integral imposes on its parts.

$$n_{\text{inner}} = 1.599 + 0.04568\cdot\text{air},\qquad R^2 = 0.9527,$$

i.e. one interior prime per 21.9 of air (mean interior gap 20.9 against $\log 10^9 = 20.7$). The
subset-number sequence behaves as a memoryless packing:

| quantity | measured | model |
|---|---|---|
| primes per block touched | 1.36 | — |
| share of consecutive inner primes in the same 30-block | **0.490** | $1-\mathbb{E}[\min(g,30)]/30 = 0.47$ (exponential spacing, mean 20.9) |
| blocks touched per 13.85 primes | 10.17 | 9.67 blocks spanned, so at most 10.7 — the primes fill the span almost completely |

So the subset-number sequence is a Poisson-like walk: zeros (two primes in one block) at 49%, which is
what an exponential spacing of mean 20.9 puts there. There is no extra packing.

## 6. Causality, stated as the data allow

* **Caused (arithmetic, zero exceptions):** the *boundary* gaps' end digits, through the endpoint
  residues mod 30 and the mod-5 exclusion; the sum of all interior digits, through air; the absence of
  2-gaps; the mod-6 alternation.
* **Caused in the other direction (graded, measured):** the interior's *statistics* — count, digit mix,
  mean gap, block reuse, composition spread — are all set by the total (§4a). The interior's *particulars*
  are not, and the interior does not predict the class.
* **Nearly nothing forward:** the interior predicts the *next* segment's class at 0.004 bits above a
  null of 0.001 — that is the 30-block autocorrelation already measured (0.015 bits), not new
  information.

The one-line version: **the segment's endpoints write its first and last gap digits; the length writes
its contents; nothing else writes anything.** The end digits and subset numbers inside a segment
correlate with the class exactly as far as 30-block bookkeeping forces them to, and not one bit further.
