# The twin-segment end-digit key (IMG_5933): decoded and verified

You were right that this is a different object from the base key. It decodes exactly, and it is
correct. Test data: 3,424,504 handoffs between consecutive twin pairs below $10^9$.

## The definition that fits

For consecutive twin pairs $(p,p+2)$ then $(q,q+2)$:

* **label** = (last digit of $p$ : last digit of $q+2$) — the jump from the **beginning** end digit of
  one segment all the way to the **endpoint** end digit of the next;
* **header** = the combined total, $T=(q+2)-p$ — everything from the first node to the last, not just
  the air between the pairs.

That total is the air plus the two pair members:
$$T = \big(q-(p+2)\big) + 4 = \text{air} + 4 .$$
**This is why the twin headers and the prime headers differ by four.** The base-key floors are
$\{4,10,16,22,28\}$; the twin-key floors are $\{8,14,20,26,32\}$ — the same five classes, shifted by 4.

## Verification: nine labels, five classes, no exceptions

| label | total $\bmod30$ | minimum total | count $<10^9$ |
|---|---|---|---|
| 1:9 | 8 | 8 | 407,384 |
| 7:1 | 14 | 14 | 405,170 |
| 9:3 | 14 | 14 | 404,467 |
| 1:1 | 20 | 20 | 378,724 |
| 9:9 | 20 | 20 | 379,427 |
| 7:3 | 26 | 26 | 381,641 |
| 1:3 | 32 | 32 | 355,108 |
| 7:9 | 32 | 32 | 355,317 |
| 9:1 | 32 | 32 | 357,265 |

Every label falls in exactly one residue class, and the minimum total equals the class. Labels at class
8 and 26 are singletons, classes 14 and 20 carry two labels, class 32 carries three. That is forced, not
empirical: the pair-start digit is in $\{1,7,9\}$ and the pair-end digit is in $\{1,3,9\}$, so the nine
labels are exactly the $3\times3$ grid, and $T\bmod30$ is a function of the digit jump plus the pair
structure.

## The page, completed

Your columns as read, with what the arithmetic fills in:

| header | your entries | complete set |
|---|---|---|
| 8 | 5:3, 1:9 | ✔ (5:3 is the single start at 5: $5\to13$, total 8) |
| 14 | 7:1, 9:3 | ✔ complete |
| 20 | 1:1 | **add 9:9** |
| 26 | 7:3 (+ 7:9, 9:1, 1:3 as read) | 7:3 only; the other three are class 32 |
| 32 | 1:3, 9:1, 7:9 | ✔ complete |
| 38 | 1:9 | ✔ |
| 44 | 9:3 (header written 24) | **add 7:1**; header is 44 |
| 50 | 9:9, 1:1 | ✔ complete |
| 56 | 7:3 | ✔ |
| 62 | 1:3 | **add 7:9, 9:1** |

The second octave (38, 44, 50, 56, 62) is the same five classes 30 further out, so its entries must
mirror the first octave's. Where your page already shows both octaves for one class (e.g. 50 vs 20)
they agree.

## The inner-node count, filled in

`C` = number of primes strictly inside the jump (the "inner nodes"). Your counter, tabulated:

| label | class | n | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12+ | median | max |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1:9 | 8 | 407,384 | 39,137 | 22,212 | 24,254 | 23,446 | 23,184 | 22,431 | 20,349 | 17,945 | 15,592 | 13,599 | 12,428 | 11,668 | 161,139 | 8 | 176 |
| 7:1 | 14 | 405,170 | 42,836 | 30,070 | 27,875 | 23,351 | 20,106 | 17,860 | 16,508 | 15,410 | 14,508 | 13,765 | 13,437 | 12,684 | 156,760 | 8 | 178 |
| 9:3 | 14 | 404,467 | 42,566 | 30,290 | 27,879 | 23,332 | 19,980 | 18,004 | 16,399 | 15,577 | 14,485 | 13,734 | 13,034 | 12,484 | 156,703 | 8 | 176 |
| 1:1 | 20 | 378,724 | 21,700 | 22,650 | 20,191 | 20,656 | 20,446 | 20,464 | 19,878 | 19,001 | 17,245 | 15,596 | 13,711 | 12,054 | 155,132 | 9 | 192 |
| 9:9 | 20 | 379,427 | 21,434 | 22,751 | 20,556 | 21,086 | 20,677 | 20,264 | 19,689 | 18,741 | 17,365 | 15,753 | 13,708 | 12,128 | 155,275 | 9 | 181 |
| 7:3 | 26 | 381,641 | 21,794 | 28,271 | 26,052 | 25,070 | 22,270 | 18,923 | 16,491 | 14,596 | 14,208 | 13,577 | 13,139 | 12,720 | 154,530 | 9 | 179 |
| 1:3 | 32 | 355,108 | 15,143 | 23,855 | 21,175 | 18,728 | 17,596 | 16,658 | 16,033 | 16,150 | 15,591 | 14,928 | 14,028 | 12,586 | 152,637 | 10 | 175 |
| 7:9 | 32 | 355,317 | 15,126 | 24,036 | 20,993 | 18,588 | 17,566 | 16,641 | 16,200 | 15,941 | 15,664 | 15,007 | 13,942 | 12,579 | 153,034 | 10 | 202 |
| 9:1 | 32 | 357,265 | 14,550 | 23,974 | 21,115 | 18,439 | 17,352 | 16,535 | 16,612 | 16,688 | 16,096 | 15,406 | 14,288 | 12,867 | 153,343 | 10 | 182 |

The zero-node cells are the tight constellations: class 8 with $T=8$ is one of these,

$$\{0,2,6,8\}\ \text{relative to the first node}\ (11,13,17,19),$$

class 14 with $T=14$ is $\{0,2,12,14\}$, class 32 with $T=32$ is $\{0,2,30,32\}$ — two pairs with nothing
between them but each pair's own partner. Class 8 has the most of these (39,137) because it has the
smallest minimum total.

## The plasma-shield reading, measured

If the jump is the ship's envelope and the inner gaps are the fluid being pushed around it, then the
fluid's thickness is the node count and its pressure is the gap per node:

| class | mean total $T$ | mean nodes | nodes / total |
|---|---|---|---|
| 8 | 283.6 | 12.38 | 0.0437 |
| 14 | 277.5 | 12.09 | 0.0436 |
| 20 | 298.8 | 13.08 | 0.0438 |
| 26 | 290.5 | 12.67 | 0.0436 |
| 32 | 308.4 | 13.50 | 0.0438 |

Flat to 0.5% across all five classes. So **the key sets the quantum of the envelope, not the thickness of
the fluid**: once you fix the class, the node count follows the total and the local spacing, and the label
adds nothing. The pressure confirms it: mean gap per node $=21.23$ against $\log 10^9 = 20.72$.

The fluid is also not a smooth shell. Node counts against a Poisson with the same mean (12.85) are
wildly over-dispersed: $P(0\ \text{nodes}) = 0.0684$ where Poisson gives $2.6\times10^{-6}$, and the Fano
factor is 13.45. The range runs from 0 nodes to **202 nodes** (total gap up to 4,772). What makes the
thickness fluctuate is the exponential waiting time for the next pair, not any organised wave around the
ship. The envelope is quantised, and its contents are noise at every scale — which is what the
autocorrelation test found independently: $0.015$ bits carried from one 30-block to the next.
