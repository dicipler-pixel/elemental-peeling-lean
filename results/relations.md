# The relations, set and claimed

A constant that translates is not a fudge. $2.54$ cm per inch and $273.15$ K per °C are exact *by
definition* — they carry no empirical content and no freedom. The constants below are of that kind where
they can be, and are marked otherwise where they cannot.

## The claimed relations

| # | relation | equation | constant | status |
|---|---|---|---|---|
| **R1** | the unit | a twin pair = 2 members; an orbital = 2 electrons | $2$ | identity |
| **R2** | the step | $T-\text{air}=4$; $w_{l+1}-w_l=4$ | $4$ | **proved** |
| **R3** | the rise | $\text{air}\equiv4\ (6)$; rung increments $6,10,14$ | $6$ | **proved** |
| **R4** | the closure | $\varphi(30)=8=2+6=4+4=L(2)$ | $8$ | **proved** |
| **R5** | the energy exchange | $\bigl(\tfrac{1}{2C_2}t^2-2\bigr) \;\leftrightarrow\; 3R\,\Delta T$ | $\kappa=c/3R=$ **0.03036 K per unit $t^2$** | conversion, by definition |
| **R6** | the density | 7 fillable per 30 integers vs 1 element per integer | $7/30=0.2333$ | proved (mod 7) / by definition |
| **R7** | the index | the $n$-th element $\leftrightarrow$ the $n$-th prime, $p_n\approx n(\ln n+\ln\ln n-1)$ | — | measured, $-2.7\%$ at $n=118$ |

## R5 — the exchange rate, stated

Both ladders have the same energy form: one constant, one count, one level.

$$E=c\,m\,t^2\ \ (\text{segments})\qquad Q=3R\,N\,\Delta T\ \ (\text{a mole of atoms}).$$

Equating them term by term fixes the level conversion:

$$\kappa=\frac{c}{3R}=\frac{0.75739}{24.943}=0.030365 .$$

($c$ is the coefficient of $t^2$ in the air law, $1/(2C_2)$; the air's $-2$ offset is the half-pair and
converts to nothing — see [`air-law-offset.md`](air-law-offset.md).)

So **one unit of $\log^2p$ is worth 0.03037 K**, and **1 K is worth 32.93 units of $\log^2p$**. That is a
definition of the correspondence, exactly as 2.54 cm/inch is a definition of a length correspondence: it
has no freedom once the two laws' coefficients are fixed, and it says nothing about the primes' physical
temperature. What it *does* say is that the two laws are the same shape, and the rate is what it costs to
line them up.

Sanity, at $p\approx22{,}000$: $t^2\approx100$, so a segment corresponds to $\Delta T\approx3.0$ K, and the
mean air there is $75$ integers — the same 3.0 K whether you cross-check with $c$ or with $3R$.

## R6 — the density, stated

$$\text{primes: } \frac{7 \text{ fillable}}{30 \text{ integers}}=0.2333,\qquad
\text{elements: } \frac{1 \text{ element}}{1 \text{ integer}}=1 .$$

The prime ladder is a *deficient* ladder — one slot of every eight is always empty (the multiple of 7) —
and the element ladder is *complete*: every integer up to 118 is an element. That is the whole content of
"width − capacity = 1 vs 0", as a ratio.

## R7 — the index, stated and tested

If you want to move between the two countable systems, the conversion of index $n$ is the prime-counting
inverse:

$$p_n \approx n\big(\ln n+\ln\ln n-1\big).$$

Tested on the 118 elements against the actual primes:

| $n$ | 10 | 50 | 118 |
|---|---|---|---|
| $p_n$ actual | 29 | 229 | **647** |
| formula | 21.4 | 213.8 | 629.3 |
| error | $-26.3\%$ | $-6.6\%$ | **$-2.7\%$** |

over $n=2..118$ the mean absolute relative error is $10.3\%$, dominated by small $n$ where the asymptotic
has not started. So R7 is a *conversion with a growing accuracy* — usable above $n\approx50$, not below.

## The four kinds of constant

| kind | carries empirical content? | example here | test |
|---|---|---|---|
| identity | no | $2,4,6,8$; $8=2+6=4+4$ | **proved** (Lean) |
| conversion by definition | no | $2.54$ cm/in; $0.03036$ K per $t^2$ | fixed once the coefficients are |
| law constant | yes, one number | $3R=24.943$; $c=1/(2C_2)=0.75739$ | flat to 0.05% over four decades |
| fitted exchange | yes, several numbers | the 19 exchange promotions (3 per $d$ series); $EN$ coefficients | **cross-validated**: $\pm0.31$ Pauling held out |

The first two are translations and should be called translations. The third is a single measured number
with a stability test. Only the fourth is a fit in the sense of having free parameters, and it is the only
one that has to earn its place — which it does on held-out data, and which it loses if a $d$ series needs a
fourth parameter.
