# The periodic table of the primes: 8 columns, subset number as the row

The element table's shape is forced by $2(2l+1)$ and $2n^2$. Run the same idea on the primes and the
table is a **strip**: eight columns, one row per 30-block, unbounded below. Everything in this note is
measured below $10^9$ (50,847,534 primes); the arithmetic claims are proved in the text.

## The grid

Columns are the eight admissible residues mod 30; the row index is the **subset number**
$s=\lfloor p/30\rfloor+1$, first row $s=1$. Full grid for the first 30 rows in
[`tableG_prime_table.csv`](tableG_prime_table.csv); per-column statistics in
[`tableH_prime_column_stats.csv`](tableH_prime_column_stats.csv).

| subset | 1 | 7 | 11 | 13 | 17 | 19 | 23 | 29 |
|---|---|---|---|---|---|---|---|---|
| 1 | · | 7 | 11 | 13 | 17 | 19 | 23 | 29 |
| 2 | 31 | 37 | 41 | 43 | 47 | · | 53 | 59 |
| 3 | 61 | 67 | 71 | 73 | 79 | 83 | 89 | · |
| 4 | 97 | · | 101 | 103 | 107 | 109 | 113 | · |
| 5 | · | 127 | 131 | 137 | 139 | · | 149 | · |
| 6 | 151 | 157 | 163 | 167 | 173 | 179 | · | · |

($\cdot$ is a composite or 1: the slot exists, nothing prime is in it.)

## The capacity: at most 7, and why

Write the eight entries of block $k$ as $30k+r$, $r\in\{1,7,11,13,17,19,23,29\}$. Modulo 7,
$30\equiv 2$, so the eight residues are
$$2k+\{1,0,4,6,3,5,2,1\} = 2k+\mathbb{Z}/7 \ \text{with}\ 2k+1\ \text{twice}.$$
Every residue class appears among the eight, so **at least one of the eight is a multiple of 7**, hence
composite unless it equals 7 — which happens only in block $k=0$. Therefore

> a row never fills: **capacity 7**, and capacity **6** in the blocks with $k\equiv 3 \pmod 7$, where
> two of the eight are multiples of 7 (block $k=3$: 91 and 119).

Measured over subsets 1–33: 3 rows with 7 entries, 7 with 6, 11 with 5, 7 with 4, 1 with 3, 1 with 2,
3 with none. The arithmetic bound is attained and never exceeded.

## The columns are geometric, and how exactly

Each column is a Bernoulli sequence with occupancy $q$, so its subset gaps are geometric with mean
$1/q$:

| | measured, all 8 columns | prediction |
|---|---|---|
| primes per column below $10^9$ | 6,354,987 – 6,356,475 (**0.02% spread**) | equal, from $\varphi(30)$ |
| mean subset gap | 5.2440 – 5.2452 | $\frac{8}{30}\cdot\frac{x}{\pi(x)} = \frac{8}{30}(19.667) = 5.244$ |
| $P(\text{gap}=1)$ | 0.1794 – 0.1799 | $q$, and $1/5.244 = 0.1907$ |
| largest subset gap | 62 – 81 | geometric tail, unbounded |

The mean is forced to within the equality of the column shares:
$\frac{(k_{\max}-k_{\min})}{n-1}=\frac{8}{30}\frac{x}{\pi(x)}$, and the shares agree to 0.02%. The
Hardy–Littlewood-style substitute $\frac{8}{30}(\log x-1)=5.259$ is 0.3% high — the same law, one
partial summation away.

$P(\text{gap}=1)$ sits **below** $1/\text{mean gap}$ (0.1797 vs 0.1907): adjacent blocks are 6%
less likely to both be prime than the geometric model with the same mean. That is the only departure
from geometric in the column, and I have not isolated its cause — it is the size of effect a pair
correlation between blocks 30 apart would produce, but I did not test that here.

## The carry of the gaps, in the table's own terms

A run of 1s of length $L$ is $L+1$ consecutive blocks prime in one column — an arithmetic progression
of primes with difference 30. Among any **seven** consecutive terms of such a progression one is
divisible by 7 ($30\equiv2$, invertible), so all seven are prime only if that term is 7 itself, i.e.
only for $7,37,67,97,127,157,187$ — and $187=11\cdot17$. Hence

> **the longest run is 5, and 5 is attained**: $7,37,67,97,127,157$.

Measured: every column's maximum run is exactly 5, first occurrence at $p=7$ in column 7, then at 107
(column 17), 359 (column 29), 541 (column 1). The same argument bounds a run of step $j$ at 6 when
$7\nmid j$ and at 10 when $7\mid j$ (use 11 instead of 7); only the $j=1$ bound is attained in the
measured range. This is the 2-gap carry in the table's own coordinates — a modulus forcing a hole —
and, as there, the bound is a theorem; that it is *attained* at 5 is a fact about the primes.

## What is a match of widths, and what is not

$$\varphi(30)=8 = 2+6 = \text{the } s \text{ width} + \text{the } p \text{ width}.$$

It is a coincidence of widths and nothing more ($10=\varphi(11)$ matches a block width just as well, and
$\varphi(15)=\varphi(16)=\varphi(20)=\varphi(24)=8$ as well as $\varphi(30)$). Drawn side by side the
two tables share the equation and differ in one number:

| | elements | primes |
|---|---|---|
| generator | $2n^2$, growing | $30 = 2\cdot3\cdot5$, fixed |
| width of a row | $2(2l+1)$ per block, total $2n^2$ | 8 slots |
| capacity | $2n^2$ — **closes** | 7 — **one short** |
| key | shell index $n$ | residue class mod 30 |
| promotion register | 19 named elements | the blocks where two of the eight vanish |

**Do not read the $8=2+6$ as a prediction.** Measured, a last-digit key carries $-0.142$ bits about the
block and $+0.108$ about the group (mostly parity). The widths coincide; the information does not
transfer. What transfers is the *capacity* statement — a fixed capacity reuses residue classes, a
growing one must open a new shell — and that is why an end-digit element table fails while an end-digit
prime table is exact to 0 exceptions in 224M handoffs.
