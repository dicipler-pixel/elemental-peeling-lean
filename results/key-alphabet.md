# The key alphabet is pinned by counting, not by a balance

Arithmetic is the evidence here, so the arguments below are counts and exclusions. No significance tests.

## 1. Why the twin alphabet is three, and why it cannot tip

A twin start needs $p$ and $p+2$ both coprime to 30. Take the eight wheel classes and strike the ones
that force $p+2$ to be divisible:

| class | $p+2 \bmod 30$ | killed by |
|---|---|---|
| 1, 7, 19 | 3, 9, 21 | $3 \mid p+2$ |
| 13 | 15 | $3$ and $5$ |
| 23 | 25 | $5$ |
| **11, 17, 29** | 13, 19, 31 | survive |

$$3 \;=\; 8-(4+2-1),$$

the four killed by 3, the two killed by 5, minus the one double-counted. Same shape as $16=4\cdot5-4$ and
$9=3\cdot5-6$: targets times sources, minus the exclusions.

**And the bound is attained and closed.** Twins per 30-block below $10^9$:

| twins in the block | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| blocks | 30,002,958 | 3,236,879 | 92,857 | **637** | **0** |

Three is reached 637 times and four never, and not because it is rare — because a block has only three
twin-capable residues. That is why the alphabet cannot be pushed over: there is no fourth slot for mass
to move into, so nothing tips. The capacity is the reason, exactly as with the seven-per-block bound on
the primes ($7 = 8-1$: one of the eight is always a multiple of 7).

## 2. The base alphabet is 16, and the gap end digit partitions it

The gap end digit $e=(e_p-b_g)\bmod 10$ selects a subset of the $4\times4$ table:

| $e$ | cells $(b_g,e_p)$ | count |
|---|---|---|
| 0 | $(1,1),(3,3),(7,7),(9,9)$ | **4** |
| 2 | $(1,3),(7,9),(9,1)$ | 3 |
| 4 | $(3,7),(7,1),(9,3)$ | 3 |
| 6 | $(1,7),(3,9),(7,3)$ | 3 |
| 8 | $(1,9),(3,1),(9,7)$ | 3 |
| | total | **16 = 4 + 4·3** |

So the crossing is exact in both directions:

* **the gap end digit gives a subset of the 16** — four cells for the self-class, three for each of the
  other four, and the four missing cells per non-zero class are the ones that would land on 5;
* **the 16 cells give the gap end digit back** — one class each, no ambiguity;
* and the quotient $m=(g-\delta)/30$ (the number of 30-blocks spanned) is independent of both.

## 3. Which alphabet actually differs

$$\text{primes}>5:\quad 12{,}711{,}386\ /\ 12{,}712{,}498\ /\ 12{,}712{,}314\ /\ 12{,}711{,}333
\quad\text{for } 1,3,7,9 \pmod{10},$$
$$\text{gaps}:\quad 0,2,4,6,8 \bmod 10 \ \text{at}\ 0.1793,\ 0.2298,\ 0.1983,\ 0.2188,\ 0.1738 .$$

The four prime counts differ by less than one part in ten thousand (max/min $=1.000092$); the
gap end digits do not. So the difference that lets
a key carry anything is in the **gap** alphabet, and the prime end digits are the *neutral* seat the gap
digits act on. That is the precise form of "the end digits differ": the differing one is the gap's, and
it differs between 17.4% and 23.0% — a factor $1.32$ between the largest and smallest class.

## 4. Saturation is the test of a key

| alphabet | cells | occupied | bound attained |
|---|---|---|---|
| twin type pairs | 9 | **9 of 9** | yes |
| base key cells | 16 | **16 of 16** | yes |
| twins per block | 4 possible (0–3) | 3 reached, 4 never | yes |

A key is the right key when every cell fills and the arithmetic maximum is reached. All three hold. That
is the sense in which the alphabet is *preferred*: not that it beats a rival on a score, but that it is
exactly the set of slots the residues leave, and the data occupies all of them.
