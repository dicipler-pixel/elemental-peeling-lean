# The total gap of a segment: end digit, subset number, and what each carries

The object: for consecutive twin pairs $(p,p+2),(q,q+2)$ the total gap is $T=q+2-p$ (pair to pair) or
$\text{air}=q-p-2$ (end to start). Measured on 440,309 segments below $10^8$ (and 3.4M below $10^9$ for
the transition table).

## 1. The two totals live in the two different alphabets

$$\text{air}\equiv 4 \pmod 6 \ \Rightarrow\ \text{air}\bmod 30\in\{4,10,16,22,28\}\quad(\text{base key}),$$
$$T\equiv 2 \pmod 6 \ \Rightarrow\ T\bmod 30\in\{2,8,14,20,26\}\quad(\text{twin key}).$$

Zero exceptions in 3.4M segments. So "the gap between the pairs" and "the gap between the pair starts"
are the same number shifted by 4, and the shift moves it from one key's alphabet to the other's. That is
the mechanical reason a base-key floor reappears as an air class and a twin-key class as a $T$ class —
and it is the precise form of "28 is a total, not a column": every air is one of $4,10,16,22,28$.

## 2. The end digit of the total gap is a relabelling of the pair-type transition

The five residues are **not** equally likely:

| air mod 30 | 28 | 10 | 16 | 4 | 22 |
|---|---|---|---|---|---|
| share | **30.7%** | 24.0% | 22.1% | 12.1% | 11.1% |

These are exactly the counts of the type transitions, aggregated by difference:

| type step | pairs | count | share |
|---|---|---|---|
| $0$ (same type) | $11\to11$, $17\to17$, $29\to29$ | 135,279 | **30.7%** |
| $12$ | $17\to29$, $29\to11$ | 105,821 | 24.0% |
| $18$ | $11\to29$, $29\to17$ | 97,287 | 22.1% |
| $6$ | $11\to17$ | 53,095 | 12.1% |
| $24$ | $17\to11$ | 48,827 | 11.1% |

So the end digit of the total gap carries **no information beyond which type step occurred**, and the
non-uniformity is entirely that: three type transitions of weight $0.31+0.12+0.11$ produce air
$\equiv 28$, and the other two classes are single steps.

## 3. What the end digit correlates with: essentially nothing

| tested against | mutual information | permutation null |
|---|---|---|
| subset gap $m=\lfloor \text{air}/30\rfloor$ | **0.0085 bits** | 0.00007 |
| number of inner primes | 0.0109 bits | 0.00034 |
| count of inner gaps ending in 0 | 0.0050 bits | 0.00008 |
| count of inner gaps ending in 6 | 0.0205 bits | 0.00009 |

All below $2\%$ of the 2.3 bits a digit holds. The only real associations are the two forced ones: the
sum of the interior digits equals the end digit mod 10, and the next segment's end digit (the $5\times5$
transition table of `inside-the-segment.md`, six forced zeros).

## 4. The subset number of a total gap is the quotient, and it is memoryless

$$\text{air}=30m+r,\qquad m=\Big\lfloor \frac{\text{air}}{30}\Big\rfloor,\quad r\in\{4,10,16,22,28\}.$$

$m$ is the number of 30-blocks the segment spans. Its distribution is exponential to 1%:

| $m$ | 0 | $\le1$ | $\le2$ | $\le5$ | $\le10$ | $\le20$ |
|---|---|---|---|---|---|---|
| measured | .113 | .222 | .321 | .549 | .774 | .945 |
| exponential, same mean | .125 | .234 | .330 | .551 | .769 | .939 |

mean $m=6.92$, sd $7.22$ (exponential would give sd $=7.50$). So the block-count of a segment is
memoryless — there is no preferred size.

Correlations of $m$: with the number of inner primes **1.008 bits**, which is not information but the
same fact twice ($m$ is the length in blocks, the inner count is the length in primes); with the end
digit $r$ it is $0.0085$ bits, all of it from the corner $m=0$ where the remainder is the whole number.

## 5. A correction this forced: the circulation is a low-$x$ transient, not a steady state

The type transition matrix is **circulant** at every scale — the three edge ratios agree to five parts in
ten thousand ($1.0645$, $1.0650$, $1.0650$ at $10^9$). But its rotation bias is not constant:

| window | forward | reverse | forward/reverse | self-share |
|---|---|---|---|---|
| $10^3$–$10^4$ | 69 | 58 | 1.190 | .253 |
| $10^4$–$10^5$ | 389 | 336 | 1.158 | .289 |
| $10^5$–$10^6$ | 2,661 | 2,210 | 1.204 | .299 |
| $10^6$–$10^7$ | 18,775 | 16,668 | 1.126 | .302 |
| $10^7$–$10^8$ | 137,007 | 126,835 | 1.080 | .308 |
| $10^8$–$10^9$ | 1,058,105 | 993,678 | 1.065 | .312 |

The excess decays monotonically — $1.35/\log x$ fits the top three windows to 10% — so the $\pm$ circulation
reported earlier is a finite-range effect that is going away, not a non-equilibrium steady state. What
*is* scale-stable is the self-share: $0.311$ at $10^9$, essentially the same at $10^6$. A walk that stays
with probability $1/3$ and rotates otherwise is the steady structure; the direction of the rotation is
not.
