# The 1·3·7·9 scale, and how it sets the specific heat of a segment

The four live digits are not four equivalent classes. A twin pair uses two of them, and which two is
fixed by the pair type:

$$\text{type } 13=(1,3),\qquad 79=(7,9),\qquad 91=(9,1).$$

So digit **1** and digit **9** can open or close a pair, **3** can only close one, **7** can only open
one. A segment joins the close of one pair to the close of the next, so it is labelled by
$(b_g,e_p)\in\{1,7,9\}\times\{1,3,9\}$ — nine cells, and the nine are exactly the $3\times3$ type
transition table.

## 1. Each of the nine cells is one type step, and the step kind sets the heat

With $T=q+2-p$ the pair-to-pair total and $t=\log p$, each cell has its own specific heat
$c=\sum T/\sum t^2$ (measured below $10^9$, 3,424,503 segments):

| cell | type step | kind | segments | mean $T$ | $c$ |
|---|---|---|---|---|---|
| 1→3 | $13\to13$ | **self** | 355,108 | 307.7 | 0.7967 |
| 7→9 | $79\to79$ | **self** | 355,317 | 308.4 | 0.7978 |
| 9→1 | $91\to91$ | **self** | 357,265 | 309.1 | 0.7998 |
| 1→1 | $13\to91$ | back | 378,724 | 298.6 | 0.7732 |
| 7→3 | $79\to13$ | back | 381,641 | 290.5 | 0.7537 |
| 9→9 | $91\to79$ | back | 379,427 | 299.1 | 0.7755 |
| 1→9 | $13\to79$ | **forward** | 407,384 | 283.6 | 0.7374 |
| 7→1 | $79\to91$ | **forward** | 405,170 | 277.4 | 0.7214 |
| 9→3 | $91\to13$ | **forward** | 404,467 | 277.5 | 0.7212 |
| | | all | 3,424,503 | 294.0 | **0.7627** |

The nine values fall into three tight groups, and the grouping is the cycle $13\to79\to91\to13$:

| kind | cells | $c$ | mean $T$ | deviation from 0.7627 |
|---|---|---|---|---|
| self (the type repeats) | 3 | **0.7981** | 308.4 | $+4.6\%$ |
| back (against the cycle) | 3 | 0.7675 | 296.1 | $+0.6\%$ |
| forward (with the cycle) | 3 | **0.7267** | 279.5 | $-4.7\%$ |

Two readings, both arithmetic rather than statistical:

* **the same-type step costs about 10% more gap than the forward step.** Same-type means the two pairs
  are 30 apart in type, i.e. $T\equiv 0 \pmod{30}$ — the largest class — and it is the *hottest*: mean
  $T=308$ against $280$ for a forward step at the same magnitude.
* **the three members of a group agree to ~0.5%** even though they are three different digit pairs
  (1→3, 7→9, 9→1). The heat follows the *kind* of step, not the digits themselves.

## 2. The anisotropy is the circulation, seen as energy

The forward step is cheaper, and the walk takes it more often ($f/r-1=+6.8\%$ below $10^9$). Both
effects decay together:

| window | self | back | forward | self/forward |
|---|---|---|---|---|
| $10^6$–$10^7$ | 0.819 | 0.771 | 0.707 | **1.158** |
| $10^7$–$10^8$ | 0.810 | 0.772 | 0.718 | 1.128 |
| $10^8$–$10^9$ | 0.798 | 0.768 | 0.727 | 1.098 |

So the drift and the heat gap are one phenomenon: **the walk is taking the cheaper transition**, and as
the cheap and expensive steps converge in price ($1.158\to1.098$), the drift decays with it
($1.35/\log x$ in `total-gap.md`). The book value of the specific heat is not a constant of the system —
it is the average over whichever mix of steps the range happens to supply.

## 3. What this gives the scale

| digit | can open a pair | can close a pair | share of twin starts |
|---|---|---|---|
| 1 | yes | yes | 1/3 |
| 7 | yes | no | 1/3 |
| 9 | yes | yes | 1/3 |
| 3 | **no** | yes | 0 |

Digit 3 is the one that never opens (no twin start $\equiv 3 \pmod{10}$) and digit 7 the one that never
closes (no twin end $\equiv 7$). The scale's asymmetry is exactly that: **two shared digits (1, 9) and
one one-sided digit at each end (7 opens, 3 closes)** — which is why the nine cells are not nine equal
things but a 3-cycle with a diagonal.

And the heat follows the cycle: diagonal $+4.6\%$, forward $-4.7\%$, back at par. A segment's energy is
therefore predicted to $\pm5\%$ from its digit transition alone, before any measurement of the gap.
