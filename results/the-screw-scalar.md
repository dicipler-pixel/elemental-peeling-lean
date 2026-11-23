# The screw scalar: one number, both parts

You were right and my "two coordinates" was a statement about *linear* models only. The scalar exists,
it is monotone in $Z$, it carries the period as its integer part and the countdown as its fractional
part, and it predicts better than the pair.

## 1. The scalar

$$S(Z)=m+\frac{L(m)-h}{L(m)+1},\qquad h=C(m)-Z,\qquad L(m)=2\Big\lceil\tfrac{m+1}{2}\Big\rceil^2 .$$

The denominator $L+1$ (rather than $L$) keeps the noble gas strictly inside the turn, so no element lands
on an integer. Then

$$m=\lfloor S\rfloor,\qquad h=L(m)-(S-m)\big(L(m)+1\big)$$

— **both parts are recovered from the single number**, checked on all 118. $S$ is strictly increasing in
$Z$ (verified element by element), and it runs $1.333\to7.970$: one turn per period, seven turns in all.
That is the screw: a monotone height with a trackable phase, which is exactly the "base 0 from monotone
$Z$, periodic from $h$" construction.

## 2. What the one number predicts

$R^2$ of a linear model whose regressors are $S$ and a polynomial in its phase
$f=S-\lfloor S\rfloor$ (main group, log $y$ for $IE_1$ and radius):

| model | EN | $IE_1$ | radius | mass | heat | mean |
|---|---|---|---|---|---|---|
| $S$ alone | 0.050 | 0.185 | 0.349 | 0.920 | 0.235 | 0.348 |
| **$S$ + phase$^1..3$** | 0.826 | **0.809** | 0.643 | 0.932 | 0.490 | **0.740** |
| **$S$ + phase$^1..5$** | **0.864** | **0.825** | 0.670 | 0.933 | 0.499 | **0.758** |
| (group, period), two coordinates | 0.816 | 0.648 | 0.604 | 0.902 | 0.502 | 0.694 |

**One coordinate beats two**, on every property except the molar heat, and on $IE_1$ by 0.16. The reason
is not that one coordinate is more informative — $(g,m)$ and $S$ carry the same information — but that the
function is *smooth in $S$'s phase* while $g$ is a step across blocks: the phase captures the s-block's
long countdown nonlinearly, and $g$ cannot.

So the corrected statement: **a single scalar suffices, provided the model is allowed to be a polynomial
in its phase.** "Two coordinates are needed" was true of linear models and false of the object.

## 3. What cannot happen — corrected

**I had this wrong and the data say so.** I wrote "valence 9 is impossible (the octet)". A shell
occupation of 9 occurs in **eleven element-shells** of the measured table:

| element | shells | where the 9 sits |
|---|---|---|
| Sc | 2, 8, **9**, 2 | $3s^23p^63d^1$ |
| Y | 2, 8, 18, **9**, 2 | $4s^24p^64d^1$ |
| La, Lu, Ac | …, **9**, 2 | the $d^1$ of the third transition row |
| Ce, Pa, U, Np | …, **9**, 2 | $f$/$d$ mixed configurations |
| Gd, Cm | …, **9**, 2 | half-filled $f$ with a $d$ electron |

So 9 is not excluded on the element side at all — it is an ordinary count, and the correction is stronger
than the objection: it is not only ionic (Cu²⁺ is $3d^9$, Ag²⁺ is $4d^9$), it is in the *neutral ground
states*. And the outermost occupied shell reaches **18** in Pd (no $5s$ electrons), so the octet is not
even a bound on the outer count.

The right bound is the capacity, and it is not 8 — it is $2n^2$:

| shell | max occupation in the 118 | $2n^2$ |
|---|---|---|
| 1 | 2 | 2 |
| 2 | 8 | 8 |
| 3 | 18 | 18 |
| 4 | 32 | 32 |
| 5 | 32 | 50 |
| 6 | 18 | 72 |
| 7 | 8 | 98 |

Every maximum is at or below $2n^2$, and 9 fails only against the $n=2$ capacity of 8. Ions add electrons
(the "stolen" ones) and the capacity is what bounds them, not the octet.

**What survives of the exclusion claim**, and it is narrower than I stated:

| exclusion | holds? | witness |
|---|---|---|
| prime end digit 5 | **yes** | $5\mid p$ — a divisor |
| twin start 3, twin end 7 | **yes** | $5\mid p+2$ |
| capacity ending in 1,3,7,9 | **yes** | every capacity counts pairs |
| a count of 9 | **no — refuted** | 11 element-shells, plus Cu²⁺ $d^9$ |

So the element side excludes nothing about the digits; it excludes the *capacities* from being odd. The
digit dichotomy is one-sided: the primes forbid a digit (5), the elements forbid only their books.

## 4. What this changes in the record

* this file's own §3 was wrong about 9 and is corrected above;
* `which-coordinate.md` said "no scalar works; two are needed". **Corrected here**: no *linear* scalar
  works; the screw scalar with a phase polynomial does, and does better.
* The universal scale's second axis is not a *second* coordinate — it is the phase of the first. The
  scale is one number.
