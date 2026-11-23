# Reading the sheet back: the T column, the two excesses, and the digit correlation

Both of your statements check out, and the sheet turned out to be a table in the record's own
coordinates. Here is what it says, computed rather than read.

## 1. What the sheet is

Primes 347–859 in rows, the gap written above each prime, the twin starts and their partners marked in
pink — and the numbers over each marked pair are the **totals** of the twin segments:

$$T=(q+2)-p .$$

Every one of the thirteen totals written on the sheet matches the computed value exactly
(`scripts/sheet_readback.py`):

| twin starts | 347 | 419 | 431 | 461 | 521 | 569 | 599 | 617 | 641 | 659 | 809 | 821 | 827 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $T$ computed | 74 | 14 | 32 | 62 | 50 | 32 | 20 | 26 | 20 | 152 | 14 | 8 | 32 |
| on the sheet | 74 | 14 | 32 | 62 | 50 | 32 | 20 | 26 | 20 | 152 | 14 | 8 | 32 |

So the sheet is the twin-segment ladder written out prime by prime, with the air and the total in the
record's own units. The last $T$ on that span would be 26 (857 → 881); the sheet stops at 32.

## 2. The excess — and it is two different excesses

**(a) The overlap of the rows.** The rows share their boundary primes: 419 ends one row and starts the
next, and the same for 461, 521, 599, 659, 809. That is **6 shared primes for 7 rows**, i.e. $R-1$. So a
model that sums "primes per row" over-counts by exactly $R-1$ — countable, and the sheet shows it.

**(b) The overlap of the totals.** Summing $T$ is not summing a distance, because each segment supplies
two of its own:

$$\sum_{i=1}^{n}T_i=\bigl(p_{n+1}-p_1\bigr)+2n .$$

On the sheet: $\sum T=536$ and the span is $857-347=510$, so $536=510+26=510+2\cdot13$ ✔
(Lean: `totals_excess`, `totals_span`). The excess over the span is **two per segment** — the two
members of the pair — and that is the "beginning and end" you are pointing at: $T=\text{air}+4$, with a
$+2$ at each end.

So the two corrections are different in kind, and both are exact: **$2$ per segment** (the pair width) and
**$1$ per shared row boundary** (the indexing).

## 3. The end digits do correlate — with the prime just outside, and only there

Measured on 148,929 consecutive prime pairs (below $2\times10^6$), the transition matrix of end digits
$P(\text{next}\mid\text{this})$, against the null $0.2500$:

| this ↓ next → | 1 | 3 | 7 | 9 |
|---|---|---|---|---|
| **1** | **0.164** | 0.318 | 0.329 | 0.189 |
| **3** | 0.225 | **0.147** | 0.296 | 0.332 |
| **7** | 0.258 | 0.276 | **0.148** | 0.318 |
| **9** | **0.351** | 0.260 | 0.228 | 0.161 |

The diagonal is suppressed to 0.147–0.164 (a repeat needs a gap of 10, 20, …) and two off-diagonal
entries are enhanced: $9\to1$ at 0.351 and $3\to9$ at 0.332. So the digit of the prime just before a
segment *does* predict the first digit inside it — and, read transposed, the digit just after predicts the
last one. Your sentence is exactly this matrix applied at the two ends.

**And it reaches two or three primes, not further.** Maximum deviation from uniform, by lag:

| lag | 1 | 2 | 3 | 4 |
|---|---|---|---|---|
| max $\lvert P-0.25\rvert$ | 0.103 | 0.037 | 0.007 | 0.010 |

(typical standard error 0.0013). So a segment's *ends* carry the correlation and its *interior* does not:
the dependence falls by a factor three per step and is at the noise floor by the third prime.

## 4. Where this sits in the record

The 4×4 matrix **is** the base key's 16 cells — departing digit × arriving digit — with the counts. The
record's own version of it (below $10^9$) reports the sixteen cells saturating and the frequency falling
with the digit step: 3.90M (step 2), 3.71M (6), 3.36M (4), 2.95M (8), 2.28M (10). At the smaller range
used here the ordering is different — step 6 (24,531) leads step 2 (14,870) — which is not a
contradiction but a scale effect: the ratio of the gap-6 to gap-2 count rises as $\log p$ grows, so a
small sieve sees step 2 first and a large one sees step 6 first. The record's "frequency law" already
warns that the twin key's ordering is not monotone in the step; this is the same warning in the base key.

## 5. The consequence for the model

A model that "counts the excess" is doing two separate jobs, and they should not be merged:

1. **pair bookkeeping** — two per segment, exact, `totals_excess`;
2. **index bookkeeping** — one per shared row boundary, exact, and purely an artefact of where the rows
   were cut.

The first is physical (the two members of a pair), the second is not (the same primes, cut differently,
give a different count). Only the first is worth carrying into a law; the second disappears the moment
the cut is chosen to be the segment itself, which is the reason the record's unit is the handoff and not
the row.

*(Reproduce: `python3 scripts/sheet_readback.py`.)*
