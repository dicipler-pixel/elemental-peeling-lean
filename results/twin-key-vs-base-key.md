# Twin key vs base key: what the exclusions are and where they come from

"Twin segments can't start with a 3" — verified: 0 of 3,424,503 handoffs below $10^9$. The base key
has 3-starts everywhere: 3:7 = 3,595,468 · 3:9 = 3,840,531 · 3:1 = 3,046,813 · 3:3 = 2,229,686
(12,712,498 gaps). So the difference is real and large, and it has a reason.

## Where each exclusion comes from

A twin pair needs $p>3$, both $p$ and $p+2$ prime, so $p\equiv5\pmod6$ and $p\bmod30\in\{11,17,29\}$.
Start from the base key's eight slots and kill them one at a time:

| base slot | dies to | because |
|---|---|---|
| 1, 7, 13, 19 | **factor 3** | these are $p\equiv1\pmod3$, so $p+2\equiv0\pmod3$ |
| 23 | **factor 5** | $23+2=25\equiv0\pmod5$ |
| 11, 17, 29 | — | survive: $p\equiv2\pmod3$, $p\not\equiv0\pmod5$ |

So the twin key is the base key with **four slots killed by 3 and one by 5**, leaving three. The
"can't start with 3" is the dead slot 23 — the same hole that makes $(3,5)$ occur only once.
The mirror rule "can't end in 7" is the dead slot 5: an end digit 7 needs $p\equiv5\pmod{30}$, i.e.
$p=5$, the pair $(5,7)$.

Label counting: $16-4\,(\text{no 3 start})-4\,(\text{no 7 end})+1\,(3{:}7\ \text{counted twice})=9$.

## The identification: the label *is* the pair-type transition

The bg digit names the pair you leave; the ep digit names the pair you arrive at. Both are bijections:

| bg digit | departing pair | | ep digit | arriving pair |
|---|---|---|---|---|
| 1 | 13 = $(1,3)$, $p\equiv11$ | | 3 | 13 = $(1,3)$, $q\equiv11$ |
| 7 | 79 = $(7,9)$, $p\equiv17$ | | 9 | 79 = $(7,9)$, $q\equiv17$ |
| 9 | 91 = $(9,1)$, $p\equiv29$ | | 1 | 91 = $(9,1)$, $q\equiv29$ |

So the nine labels are the $3\times3$ matrix of pair-type transitions, and the class follows:

| label | departing → arriving | class | share | count $<10^9$ |
|---|---|---|---|---|
| 1:9 | 13 → 79 | 8 | 11.90% | 407,384 |
| 7:1 | 79 → 91 | 14 | 11.83% | 405,170 |
| 9:3 | 91 → 13 | 14 | 11.81% | 404,467 |
| 7:3 | 79 → 13 | 26 | 11.14% | 381,641 |
| 9:9 | 91 → 79 | 20 | 11.08% | 379,427 |
| 1:1 | 13 → 91 | 20 | 11.06% | 378,724 |
| 9:1 | 91 → 91 | 32 | 10.43% | 357,265 |
| 7:9 | 79 → 79 | 32 | 10.38% | 355,317 |
| 1:3 | 13 → 13 | 32 | 10.37% | 355,108 |

The diagonal of the twin key — 1:3, 7:9, 9:1 — is the self-handoffs, and they are the three rarest.

## Warning: the same nine pairs mean different things in the two keys

| label | in the base key | in the twin key |
|---|---|---|
| 1:3 | a single step of 2 (twin primes), the *most* common gap | 13 → 13, a self-handoff, the *least* common |

The base key's labels are prime→prime digit pairs; the twin key's are pair→pair type codes. Same
symbols, different referents. In writing, distinguish them (e.g. `1:3` vs `13→13`), or the two
tables will silently contradict each other — 1:3 is the commonest thing in one and the rarest in the
other.

## Two more consequences, both measured

**Frequency law.** In the base key, per-label frequency falls monotonically with the digit step:
3.90M (step 2) → 3.71M (6) → 3.36M (4) → 2.95M (8) → 2.28M (10). In the twin key it is **not**
monotone in the step, because it is the transition matrix:
1:9 (step 8) is *commoner* than 1:1 (step 0). Range across the nine labels is 10.37%–11.90%.

**Resolution.** Within a class the labels are interchangeable: class 14 spread 0.17%, class 20
spread 0.19%, class 32 spread 0.61%, against a between-class spread of 14.7%. So the class carries
essentially all the information in the twin key, and the label within a class adds under a percent.
That is consistent with the value ladder: $V$ is a bijection on classes, and within a class the three
labels 1:3, 7:9, 9:1 share a value because they genuinely behave the same.

## The nesting statement

* label sets: twin $\subset$ base, 9 of 16 cells.
* class maps: **not** nested — the twin class is the base class $+4$ in the gap ($T=\text{air}+4$),
  which is $+3$ on the value ladder.
* class multiplicities: base $(3,3,3,3,4)$, twin $(1,2,2,1,3)$.
* the single label carrying a 5 is 5:3, the one jump from the prime 5 to 13 (total 8) — the only
  entry in either table with a 5, and the reason your 8 column has two rows.
