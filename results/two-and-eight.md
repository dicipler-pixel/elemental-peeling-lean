# What 2 and 8 do

If 6 and 4 are the steps of both ladders, then 2 and 8 are its **ends**: 2 is the unit everything is
measured in, 8 is the first closure everything is measured to. And the two ends are linked by an identity
that holds two ways at once.

## 1. 2 is the unit — and it is why every capacity is even

$$w_l=2(2l+1),\qquad \sum_{l<n}2(2l+1)=2n^2,\qquad L(m)=2\Big\lceil\tfrac{m+1}{2}\Big\rceil^2 .$$

Every capacity is $2\times$ an integer. That is Pauli (one orbital, two electrons), and it is the reason
for the dichotomy proved in Lean: **no capacity can end in 1, 3, 7 or 9.** The widths are $2\times$ the
*odd* numbers, i.e. the orbital counts:

| $l$ | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| width | 2 | 6 | 10 | 14 | 18 |
| orbitals $2l+1$ | 1 | 3 | 5 | 7 | 9 |

On the prime side 2 plays the same role: a twin pair spans 2, a segment is $2+\text{air}+2$, and
$\text{air}=q-p-2$ — the 2 subtracted is one pair member, as the 4 subtracted from $T$ is one whole pair.

**And 2 is the column multiplicity.** Each of the four live last digits owns exactly two of the eight
columns:

$$\{1,11\},\quad \{13,23\},\quad \{7,17\},\quad \{19,29\}.$$

So $4=8/2$, and the base key's 16 cells are $2\times8$ as well as $4\times4$.

## 2. 8 is the first closure

$$8 \;=\; 2n^2\big|_{n=2} \;=\; \varphi(30) \;=\; \text{the octet} \;=\; L(2)=L(3) \;=\; T_{\min},$$

where $T_{\min}=8$ is the smallest twin total — the segment $(5,7)\to(11,13)$ with no air at all, class
8. So the first number at which a shell closes on the element side is the first number a segment can take
on the prime side. That coincidence is exact and worth stating plainly: **the octet is $T_{\min}$.**

## 3. The identity that makes the ends meet

$$8 \;=\; 2+6 \;=\; 4+4 .$$

Two readings of the same closure:

* $2+6$: the duet plus the $p$ block — the $s$ and $p$ widths, i.e. one $s$ orbital and three $p$
  orbitals, four orbitals in all;
* $4+4$: two increments of the ladder — two steps of the block increment.

So the octet is simultaneously "s + p" (a fact about blocks) and "two of 4" (a fact about the ladder's own
step). That is why 8 can be both the capacity that $h$ complements and the sum of the two widths.

## 4. The quartet is $2\times(1,2,3,4)$

$$2,\ 4,\ 6,\ 8 \;=\; 2\times(1,2,3,4) \;=\; \text{1, 2, 3, 4 orbitals}.$$

$2,4,8$ are the powers of two ($2^1,2^2,2^3$); **6 is the odd one out** — literally, since it counts three
orbitals and $6=2\cdot3$. That is why 6 appears with the $p$ block and 4 with the increment: the ladder
uses 4 (two orbitals at a time, the increment) and 6 (the $p$ block) but never 8 as a step, because 8 is
where the stepping stops.

## 5. The exclusions are built from 8

| quantity | value | from 8 |
|---|---|---|
| primes per 30-row | 7 | $8-1$ |
| twin classes | 3 | $8-5$ |
| base-key cells | 16 | $2\cdot8$ |
| octet / $v+h$ for $p$ | 8 | itself |

So the prime side's own capacity (7) and its own alphabet (3) are both $8$ minus a count of exclusions,
and the element side's octet *is* 8 — the same number, used as a bound on one side and as a total on the
other.

## 6. The four in one table

| number | role in the primes | role in the elements | character |
|---|---|---|---|
| **2** | pair width; column multiplicity | orbital pairing; $s$ width; duet | the unit |
| **4** | $T-\text{air}$: the pair pair | $w_{l+1}-w_l$: the increment | the step |
| **6** | class step | $p$ width; 3 orbitals | the step's rise |
| **8** | $\varphi(30)$; $T_{\min}$ | octet; $L(2)=L(3)$; $v+h$ | the closure |

The steps (4, 6) move the ladder; the ends (2, 8) fix what it counts and where it stops. And $8=2+6=4+4$
is the statement that the two ways of reaching the closure agree exactly.
