# Two new keys: double-twin and triple-twin merged segments

Data: all primes below $10^9$ — 3,424,505 handoffs between consecutive twin pairs.

## The definitions that make these well-posed

A **merged** handoff is one where the arriving pair is the *very next* prime after the departing
pair's partner. Nothing between them but the two partners. That is exactly your $C=0$ column:

* single twin: $(p,p+2)$
* **double twin merged**: $p,\,p+2,\,p+d,\,p+d+2$ with no prime in $(p+2,\,p+d)$
* **triple twin merged**: $p,\,p+2,\,p+d_1,\,p+d_1{+}2,\,p+d_1{+}d_2,\,p+d_1{+}d_2{+}2$ with both
  interiors empty

With $T$ the total from the first node to the last, $T=(q+2)-p$: a double is the pattern
$\{0,2,T,T{+}2\}$, and a triple is $\{0,2,d_1,d_1{+}2,d_1{+}d_2,d_1{+}d_2{+}2\}$ with
$T_{\text{triple}}=T_1+T_2-2$.

Frequency: **6.84%** of all handoffs are merged doubles (234,287 of 3,424,505); 16,046 triples.

**Census, and one correction of reading** ([`merge-and-the-count.md`](merge-and-the-count.md) §1): those
16,046 are *adjacent pairs of merges*, not three-pair segments — there are 13,982 of the latter, then 955
four-pair, 47 five-pair, 2 six-pair and 1 seven-pair segment (at $p=678{,}771{,}479$). So there are
3,190,219 segments for 3,424,506 pairs: **1.0734 pairs per segment.**

**And the merge rate is not a constant.** Measured over five decades it is
$p_{\rm merge}\cdot\langle t\rangle=1.327\pm0.016$ against $2C_2=1.32032$ — a parameter-free
prediction, because a merge is "the next prime after a pair is itself a twin", whose chance is the twin
density over the prime density, $2C_2/\log q$. So the count per segment drifts (1.139 at $10^4$ to 1.064
at $10^{10}$), and a law stated per segment inherits that 7%. The air law does not: per handoff it is
flat to 0.05% at $1/(2C_2)$.

## Key table 1 — DOUBLE TWIN

Same nine labels, same five classes as the twin key. Totals $T=\text{floor}+30k$:

| label | class | $k{=}0$ | 1 | 2 | 3 | 4 | 5 | 6 | distinct $T$ |
|---|---|---|---|---|---|---|---|---|---|
| 7:1 | 14 | 32,523 | 8,949 | 1,166 | 166 | 29 | 2 | 1 | 7 |
| 9:3 | 14 | 32,175 | 9,153 | 1,099 | 117 | 20 | 2 | — | 6 |
| 1:9 | 8 | 28,387 | 8,532 | 1,858 | 281 | 62 | 12 | 5 | 7 |
| 7:3 | 26 | 17,699 | 3,255 | 738 | 91 | 10 | 1 | — | 6 |
| 1:1 | 20 | 17,318 | 3,489 | 749 | 122 | 18 | 4 | — | 6 |
| 9:9 | 20 | 17,175 | 3,389 | 731 | 117 | 18 | 3 | 1 | 7 |
| 1:3 | 32 | 12,996 | 1,804 | 277 | 56 | 7 | 3 | — | 6 |
| 7:9 | 32 | 12,809 | 1,938 | 318 | 49 | 9 | 3 | — | 6 |
| 9:1 | 32 | 12,419 | 1,741 | 338 | 42 | 9 | 1 | — | 6 |

Floors: $T_0 = 8,14,20,26,32$ for classes $8,14,20,26,32$ — **identical to the twin key's floors.**
Pooled over labels: $k=0$ 183,502 · 1 42,250 · 2 7,274 · 3 1,041 · 4 182 · 5 31 · 6 7.
Ratio per step of $k$: 4.3, 5.8, 7.0, 5.7, 5.9 — a steep decay, not a ladder you can climb far.

Why the decay: to merge at $k=1$ you need 30 consecutive integers inside the span carrying no prime.
Its expected count is $30/\log p\approx1.45$ primes, and demanding zero of them costs roughly
$e^{-1.45}$ per step — the observed factors of 4–7 per step are that plus the stronger requirement
that the arriving pair land exactly where the residue class says.

## Key table 2 — TRIPLE TWIN

| label | class | $T$ (count) | min $T$ | distinct |
|---|---|---|---|---|
| 7:3 | 26 | 26:974 · 56:1,016 · 86:308 · 116:70 · 146:6 · 176:2 · 206:1 | 26 | 7 |
| 7:1 | 14 | 44:1,350 · 74:443 · 104:122 · 134:36 · 164:2 · 194:1 | **44** | 6 |
| 9:3 | 14 | 44:1,305 · 74:430 · 104:84 · 134:23 | **44** | 4 |
| 9:1 | 32 | 32:1,067 · 62:569 · 92:173 · 122:26 · 152:6 · 182:3 · 212:1 | 32 | 7 |
| 7:9 | 32 | 32:1,000 · 62:446 · 92:153 · 122:35 · 152:5 · 182:3 · 212:1 | 32 | 7 |
| 1:3 | 32 | 32:998 · 62:460 · 92:174 · 122:32 · 152:6 | 32 | 5 |
| 1:9 | 8 | 38:804 · 68:418 · 98:142 · 128:32 · 158:12 · 188:2 | **38** | 6 |
| 9:9 | 20 | 20:595 · 50:708 · 80:270 · 110:68 · 140:19 · 170:3 | 20 | 6 |
| 1:1 | 20 | 20:583 · 50:701 · 80:276 · 110:60 · 140:15 · 170:4 · 200:2 | 20 | 7 |
| 5:9 | — | 14:1 | 14 | 1 |

**Two of the floors move, and I can say exactly why.**

Class 14 has floor 44, not 14. A triple with total 14 needs $T_1=T_2=8$, i.e. the pattern
$\{0,2,6,8,12,14\}$ — the prime sextuplet. Mod 5 its residues are $\{0,2,1,3,2,4\}$, which is **all
five classes**, so one element is divisible by 5 and must *be* 5. That happens exactly once, at
$p=5$: $5,7,11,13,17,19$. It is in the data as the single entry **5:9 = 14:1**. For every $p>5$ the
14-triple is impossible, so the class-14 triples start at 44. Same story for class 8: 8 is impossible
($T_1+T_2=10$ has no solution with both $\ge8$), so its floor is 38.

Class 20 (20 $=8+14-2$) and classes 26, 32 are unaffected.

## The model

1. **Self-similarity.** All three levels carry the *same nine labels* ($\{1,7,9\}\times\{1,3,9\}$),
   the *same five classes* $\{2,8,14,20,26\}\bmod 30$, and the *same value ladder*
   $V=2,\,3.5,\,5,\,6.5,\,8$ for classes $32,14,26,8,20$. You do not need new labels or a new value
   scale for the deeper objects — the depth shows up only in the totals and the counts.
2. **Total law.** At every level $T\equiv2\pmod 6$ and $T\equiv$ the class $\pmod{30}$. Doubles use
   $T=\text{floor}+30k$; triples use $T=T_1+T_2-2$, which lands in the same five classes because
   $2+2-2\equiv2\pmod 6$.
3. **Merge probability.** $p_{\text{merge}}=0.0684$ per handoff, and the levels behave as independent
   draws: expected triples $=p\times$ doubles $=0.0684\times234{,}287=16{,}025$ against 16,046
   observed — 0.13% apart. So a $k$-fold merged segment has count
   $\approx N_{\text{handoffs}}\cdot p^{\,k}$, and there is no clustering of merges.
4. **The chain terminates by arithmetic, not by chance.** The one pattern that would make triples as
   common as doubles — $\{0,2,6,8,12,14\}$ — is forbidden for all $p>5$ by the factor 5 alone. The
   same argument will forbid specific patterns at every deeper level, so the hierarchy thins by a
   fixed factor per level *and* loses particular patterns outright.

## What I need from you to check the definitions

If "double twin" means something else — for instance two pairs at distance 2 (impossible: $p,p+2,p+4$
always includes a multiple of 3) or a pair plus a cousin pair — say so and I will re-run. The $C=0$
reading is the only one that is both well-defined and matches your $C$ column.
