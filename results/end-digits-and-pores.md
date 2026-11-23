# End digits, pores, and why the f/d ordering oscillates

Three tests of the "end digit and pore" reading, then the mechanism the data actually support.

## 1. End digit of Z — no association, and not a near miss

The 19 anomalies against the last digit of $Z$ (expected in brackets, from the 118-element population):

| digit | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| anomalies | 1 | 2 | 2 | 1 | 3 | 1 | 2 | 2 | 2 | 3 |
| expected | 1.8 | 1.9 | 1.9 | 1.9 | 1.9 | 1.9 | 1.9 | 1.9 | 1.9 | 1.8 |

$$I(Z\bmod 10;\ \text{anomaly}) = 0.0198\ \text{bits},\qquad \text{permutation null } 0.0644\pm0.0284,\quad p=0.955 .$$

The observed mutual information is *below* the null mean: the anomalies are more evenly spread over the
digits than chance would make them. There is no end-digit signal here, not even a weak one.

## 2. The gaps between anomalies carry the block structure, not a digit pattern

$$Z = 24,29,\ 41,42,44,45,46,47,\ 57,58,64,\ 78,79,\ 89,90,91,92,93,96$$
$$\text{gaps} = 5,12,1,2,1,1,1,10,1,6,14,1,10,1,1,1,1,3;\qquad 11\ \text{of}\ 18\ \text{are}\ \le 2 .$$

The clustering is real and it is the *crossing*: once the $d$ level is below the $s$ level (inside a
series), every subsequent element flips, so the anomalies arrive in runs. That is a property of the
block, not of the decimal digit.

## 3. The pore (capacity minus what is filled) — growing, but it does not choose the anomalies

Using the element's own shell, $\text{pore}(Z) = 2n^2 - (\text{electrons with that } n)$:

$$I(\text{pore};\ \text{anomaly}) = 0.349\ \text{bits},\qquad \text{null } 0.439\pm0.038,\quad p=0.994 .$$

Also nothing — and the reason is visible: the pore is essentially a monotone relabelling of $Z$ inside a
shell, so it cannot separate elements that sit next to each other.

**But the pore is arithmetic, and it is your ladder.** At the end of each shell:

| shell $n$ | capacity $2n^2$ | filled by $Z\le118$ | **pore** | pore $/18$ |
|---|---|---|---|---|
| 5 | 50 | 32 | **18** | 1 |
| 6 | 72 | 18 | **54** | 3 |
| 7 | 98 | 8 | **90** | 5 |

$$\text{pore}(n) = 18\,(2n-9) = 2(2\cdot4+1)\,(2n-9),$$

i.e. the unfilled space is the $g$-block width times the odd numbers $1,3,5$ — the same odd ladder as
the block widths and the twin classes. In the prime table the corresponding quantity is **1 per row and
stays 1** (capacity 7 of a width of 8). So the pore exists in both tables; in the primes it is constant,
in the elements it grows as $18(2n-9)$. That is the sharpest true version of the "mixing space" idea I
can find, and it is a statement about *shells*, not about which element flips.

## 4. What the oscillation actually is

The energy a subshell contributes depends on its occupancy through two terms:

$$\varepsilon\,k \;+\; U\binom{k}{2} \;-\; K\,\Phi(k),\qquad \Phi(k)=\binom{u}{2},\ u=\min(k,C-k).$$

The first is linear in $k$ (each electron costs the same), the second is the pairwise repulsion (costs
$U$ per pair), the third is exchange (gains $K$ per parallel pair). Only the last one is *not* monotone:
it peaks at the half-fill. Differentiating, the cost of the next electron is

$$U\,k \;-\; K\,G(k),\qquad G(k)=\Phi(k+1)-\Phi(k),$$

and $G$ is the zigzag $0,1,\dots,\tfrac{C}{2}-1,-\tfrac{C}{2},\dots,0$ — **period equal to the subshell
capacity $C=2(2l+1)$, half-period at the half-fill.** For the $f$ shell that is period 14, peak at $k=7$.

Now compare that with the $f/d$ gap $\Delta$. In the $d$ series the gap is large enough to be crossed
once, smoothly, and the exceptions form one block (`why-nineteen.md` §2–3). In the $f$ series the
constraints force $\Delta$ to run from **above $+6K$** (above $+5K$ at Sm and Pu, above $+6K$ at Eu and Am,
where the electron stays in $f$ although the step would gain $+5$, $+6$ exchange) to **below $-6K$** (at Gd and Cm, where it
leaves although leaving costs 6) — a span of more than twelve quanta, which is exactly the amplitude of
$G$ itself. Neither term dominates, so the occupancy zigzag shows straight through and the
configuration follows it. When the ruler is the same size as the thing being measured, what you see is
the thing.

That is why it oscillates: **the answer is a function of the block-relative occupation
$k \bmod 2(2l+1)$ — mod 14 for $f$, mod 10 for $d$, mod 6 for $p$ — not of $Z \bmod 10$.** Your instinct
that "a residue decides it" is right; the residue is the one the energy can see, and the energy sees only
the occupation.

$$\text{flips in } 4f:\ k\in\{0,1,7\};\qquad \text{in } 5f:\ k\in\{0,1,2,3,4,7\};\qquad k=\text{occupation before the last electron}.$$

Both sets are unions of "the head" and "the half-fill point" — the two places where the zigzag is
steepest relative to a flat rung. The difference between the two f series (two flips at the head versus
five) is how far below the $d$ level the $f$ level sits early on: $5f$ stays under $6d$ for five
electrons, $4f$ under $5d$ for only two. The usual reason offered is that $5f$ is radially more
extended and so overlaps $6d$ more strongly; I have not tested that here, and it is the natural next
check.

## 5. What would have to be true for an end-digit explanation

The anomalies would have to be a function of $Z \bmod 10$, i.e. the driver would have to be periodic in
$Z$ with period 10. It is not: the energy depends on $(n,l,k)$, and $k$ advances by one per element
while $n,l$ change at block boundaries — so the driver is periodic in $k$ with period $2(2l+1)$, which
is 6, 10, 14 for the three blocks, and 10 only for the $d$ block by coincidence of the Pauli capacity.
Any statement of the form "the anomaly is at end digit $d$" would be violated the moment two blocks with
different widths are compared, and that is what the $p=0.955$ is measuring.
