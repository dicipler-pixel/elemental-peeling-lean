# The elements' holes: three counts, kept apart

"Holes" names three different integers in this record, and most of the confusion they cause comes from
adding them. They are, separately:

| # | count | value | what it is |
|---|---|---|---|
| (i) | the element's own holes $h(Z)$ | $0$–$31$ | $L(m)-v(Z)$, the countdown: how many slots the period still has when the element sits in it |
| (ii) | the inventory's holes | **2** | $120-118$: the two slots of the rung no element fills |
| (iii) | the shells' pores at $Z=118$ | **162** | $\sum_{n=5,6,7}\bigl(2n^2-\text{electrons in shell }n\bigr)=18+54+90$ |

`scripts/element_holes.py`, [`tableV4_holes.csv`](tableV4_holes.csv).

## 1. The element's own holes: $h$, and why it is the block label

$h$ runs $0$ to $31$ over the 118 elements, total $1{,}355$ holes, mean $11.48$ per element. It is not a
free parameter — **the block is the hole interval**, and the check on all 118 elements is exact
(0 mismatches):

| block | $h$ range | elements | median $h$ |
|---|---|---|---|
| $s$ | $0$–$31$ (only $0,1$ and $L-2,L-1$) | 14 | 16 |
| $p$ | $0$–$5$ | 36 | 2 |
| $d$ | $6$–$15$ | 40 | 10 |
| $f$ | $16$–$29$ | 28 | 22 |

So "how many holes" and "which block" are the same question, which is why $h$ is the table's best single
coordinate. The seven elements with **no holes** are exactly the closures: He, Ne, Ar, Kr, Xe, Rn, Og —
$Z\in\{2,10,18,36,54,86,118\}$, the $C$'s.

And every period is full at $Z=118$: capacity $L(m)$ equals the number of elements in it for all seven
periods (2, 8, 8, 18, 18, 32, 32), which is the measured content of
[`light-bridge-theorem.md`](light-bridge-theorem.md) — the table is saturated.

## 2. The inventory's two holes

$120-118=2$. The rungs to $q=8$ hold 120 slots; the last two are the $8s^2$ that no element fills
(`rungs_to_eight`). This is the only sense in which the table has a *hole* at all: within 118 every cell
is taken (`every_cell_below_118`), so the two are an inventory fact, not a structural gap.

## 3. The shells' pores: 18, 54, 90 — and a second closing ladder

At $Z=118$ the shells hold 32, 18 and 8 electrons in $n=5,6,7$, against capacities 50, 72, 98:

$$\text{pore}(5)=18,\qquad \text{pore}(6)=54,\qquad \text{pore}(7)=90,\qquad \text{total}=162,$$

which is exactly $18(2n-9)$ — the record's law, the $g$-block width times the odd numbers $1,3,5$.

The new observation is that **the pores close on a different ladder from the table's**:

| ladder | closes at |
|---|---|
| the shells ($2n^2$) | $2,\ 10,\ 28,\ 60,\ 110,\ 182,\ 280$ |
| the table ($L(m)$) | $2,\ 10,\ 18,\ 36,\ 54,\ 86,\ 118$ |

They agree at 2 and 10 and diverge from the third: the table takes each $2n^2$ **twice**
($L(m)=2\lceil(m+1)/2\rceil^2$), so its periods close at half the shell's capacity. That is why the
table's last closure is 118 while the shells have 280 slots — the 162 pores are the difference, and they
are *outside* the table rather than holes in it. The two ladders are the same arithmetic at two different
takes on the same shell.

## 4. Does the number of holes order anything?

| property | all 118 | within $s$ | within $p$ | within $d$ |
|---|---|---|---|---|
| electronegativity | $-0.83$ | $-0.92$ | $-0.80$ | $-0.67$ |
| radius | $+0.77$ | $+0.93$ | $+0.26$ | $+0.39$ |
| molar heat $C/3R$ | $+0.57$ | $+0.62$ | $+0.02$ | $-0.07$ |

So the hole count **is** a real coordinate for electronegativity — the correlation survives inside the
blocks ($-0.67$ to $-0.92$), which is stronger than the record's original measurement suggested — and it
is **not** one for the heat capacity, where the overall $+0.57$ collapses to $+0.02$ and $-0.07$ once the
block is fixed ([`configs-vs-data.md`](configs-vs-data.md), [`specific-heat-bridge.md`](specific-heat-bridge.md)).
The hole count is therefore the coordinate to compare *chemistry* in, and not the one to compare *lattice
heat* in: a solid's heat is set by the stiffness of the lattice, which is not a count at all.

## 5. One line each

* $h$ is the number of holes in the period, and it *is* the block: $p\le5$, $d\,6$–$15$, $f\,16$–$29$,
  $s$ at $L-2,L-1$.
* The table's own holes: **2** (the unfilled $8s^2$).
* The shells' pores at 118: **162** $=18(2n-9)$ summed, closing at 2, 10, 28, 60, 110, not at the
  table's 2, 10, 18, 36, 54, 86, 118 — because the table takes each $2n^2$ twice.
* Seven elements are hole-free, and they are the seven closures.
* The hole count orders electronegativity within a block and orders the heat not at all.
