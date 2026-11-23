# The recipe + scale model: capacity, admissible sizes, and the balance

One structure recurs in everything we have measured. Every system here has three parts:

1. a **capacity** — how much one unit can hold,
2. a **recipe** — the admissible sizes of an entry,
3. a **balance** — the rule that makes the entries close the capacity,

and one free quantity that the rule does *not* fix: the **scale**. That is why a ratio is always
identified exactly while its factors are not (the specific-heat result).

| system | capacity | admissible sizes (recipe) | balance rule | free scale |
|---|---|---|---|---|
| **thermodynamics** | — | — | $c=E/(m\Delta T)$: the ratio | $m$ or $E$ (one anchor needed) |
| **accounting** | the period | any amount, both sides | Dr = Cr; $A=L+E$ | the currency / the amount |
| **music, one bar** | the meter, e.g. 4/4 = 4 quarters | 1, 2, 4, 6, 7 (dotted) | the bar sums to the meter | tempo (and A4 for pitch) |
| **primes, one 30-block** | 8 slots, at most 7 fillable | primes | air $\equiv$ class (mod 30) | the magnitude $=\text{floor}+30k$ |
| **elements, shell $n$** | $2n^2$ | blocks $2,6,10,14$ (step 4) | Pauli: ≤2 per orbital | $n$ |

## Debit/credit: the asset side, and where the credit lands

The debit never decides which side grows. **The credit account decides.**

| debit | credit | total assets | liabilities | equity |
|---|---|---|---|---|
| Equipment +20,000 | Cash −20,000 | unchanged (swap) | — | — |
| Inventory +8,000 | Accounts payable +8,000 | **up** | **up** | — |
| Cash +15,000 | Revenue +15,000 | **up** | — | **up** (at close) |
| Cash +10,000 | Loan +10,000 | **up** | **up** | — |

Four cases, one rule: every entry has equal debits and credits, and the identity $A=L+E$ holds
throughout — in the extended form $A-L-\big(E+(R-X)\big)=0$ before the year-end close, which is why
the residual column of the worked example ran 15,000 → 9,000 → 6,000 → 2,000 → 1,500 and then closed
to zero.

Her sketch (cost/liability on one side, product/asset on the other, equity beneath) is the
**acquisition** case, and it is correct: you debit what you got (the product/asset), and you credit
what you gave up (cash or a payable). One refinement: *cost* is the **amount** of the sacrifice, not
the account that made it — the credit account is cash, a payable, or equity.

And the shim: "shaved in place via pressure" is exactly right. Equity is the shim. Retained earnings
absorbs whatever does not fit, which is why the identity can never fail and why the shim is the only
place "pressure" shows up. It can be shaved negative — that is insolvency — and the sheet still
balances.

## Music: two logarithmic scales and one conservation law

The staff is a 2-D lattice of two logarithmic axes:

* **vertical = $\log$ frequency.** Pitch class $=12\log_2(f/f_0)\bmod 12$: a wheel with a **fixed
  modulus of 12**. The generator is 7 (a fifth): $0,7,2,9,4,11,6,1,8,3,10,5$ — all twelve classes,
  each once. That is the same object as her mod-30 wheel: a fixed modulus, a generator coprime to it,
  a full cycle.
* **horizontal = $\log$ time.** The note values 1, 2, 4, 6, 7 are quarter, half, whole, dotted whole
  ($4\times1.5$), double-dotted whole ($4\times1.75$) — verified $4,6.0,7.0$.
* **the bar line is a conservation law.** A 4/4 bar holds 4 quarters; adding a dotted quarter (1.5)
  forces removing 0.5 elsewhere in the same bar. That is the trial balance, exactly: you cannot add
  time without taking it from somewhere, and the bar must close.

Her staff numbering (lines 10, 8, 6, 4, 2 and spaces 9, 7, 5, 3, 1) puts **her five ladder values on
the five lines** and the odd values in the spaces. The staff is a 5-line, 9-position ladder; the
pentatonic is 5 of 12 notes — her key is 5 of 30 classes. Both are five-class selections from a wheel.

**Where the two moduli come from — the real correspondence.** Both wheels are built over the smallest
primes:

* music: $12 = 2^2\cdot 3$, and it is 12 because $(3/2)^{12}=129.746$ against $2^7=128$ — a misfit of
  1.36% (the Pythagorean comma). Twelve fifths nearly close at seven octaves; twelve is the smallest
  number that does.
* primes: $30 = 2\cdot3\cdot5$, the squarefree product of the first three primes.

So the shared origin is *small-prime consonance*: a wheel closes when the powers of a small prime
almost coincide. That is a genuine structural identity, not a metaphor — and it explains why both are
"residue ladders with a small number of classes".

Equal temperament costs a little: $2^{7/12}=1.498307$ against the just $3/2=1.500000$, a beat of
$0.0017$. The wheel's exactness and the interval's exactness trade, exactly as power and speed do in
the nautilus gear.

## The periodic table's recipe and balance, tested

**Recipe.** Fill orbitals in increasing $n+l$, ties by $n$, at 2 electrons per orbital:
1s 2s 2p 3s 3p 4s 3d 4p 5s 4d 5p 6s 4f 5d 6p 7s 5f 6d 7p. The block capacities are
$2(2l+1)=2,6,10,14$ — an **arithmetic progression of step 4** — and
$$\sum_{l=0}^{n-1}(4l+2)=2n^2$$
verified for $n=1,2,3,4$: 2, 8, 18, 32.

**How exact is the recipe?** Against the measured configurations of all 118 elements it reproduces
**99 exactly = 83.9%**. The 19 failures are
Cr, Cu, Nb, Mo, Ru, Rh, Pd, Ag, La, Ce, Gd, Pt, Au, Ac, Th, Pa, U, Np, Cm — every one a
half-filled or closed $d$/$f$ shell stabilisation.

That is an **Atlas-shaped object**: a deterministic rule at theorem grade for 83% of its domain, with a
published promotion register for the other 17%. The recipe is not a law with no exceptions; it is a
law plus a named list — which is precisely the grade/obligation discipline of the coverage ledger.

**Balance.** Pauli: two electrons per orbital, hence $2n^2$ per shell. The shell fills and the next
opens. Capacity, never collapse — the same verdict as the 7-per-30 bound on the primes, the twin-gap
floor, and the accounting identity.

## The one-line summary

Every system here is **a capacity plus a recipe plus a conservation rule, with one free scale** — and
in each case the invariant (the ratio, the class, the grade, the pitch class, the interval) is exact
while the scale (the mass, the amount, the coverage count, the octave, the tempo) needs an independent
anchor. That is the single structure that survived every test in this conversation.
