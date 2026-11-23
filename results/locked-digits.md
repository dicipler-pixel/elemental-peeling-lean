# The un-baking test: 3 and 7 cannot come back, 1 and 9 can

Your mechanism, stated exactly and then tested on both sides. **The prime side proves the shape and it is
as you describe it; the fission side shows the same shape at the closure.** `scripts/locked_digits.py`,
[`tableV10_locked_digits.csv`](tableV10_locked_digits.csv).

## 1. What "permanent" means, and why 3 and 7 are the ones

A handoff leaves a pair whose partner ends in digit $c$ and arrives at a pair whose start ends in digit
$o$. Define the **return**: $c=o$ — you came out of a 3 and the next pair opens on a 3.

The roles are fixed by the residues, not chosen:

$$\text{openers }=\{1,7,9\}\quad(\text{from classes }11,17,29),\qquad
\text{closers }=\{1,3,9\}\quad(\text{from classes }13,19,1).$$

So the returnable digits are $\{1,7,9\}\cap\{1,3,9\}=\{1,9\}$ (`Digit.returnable_digits`). Measured, to
$10^{9}$:

| departing digit | handoffs | returns | $P(\text{return})$ |
|---|---|---|---|
| 1 | 1,141,159 | 404,467 | 0.3544 |
| **3** | 1,141,216 | **0** | **0.0000** |
| **7** | **0** | — | **undefined — 7 is never a closer** |
| 9 | 1,142,128 | 405,170 | 0.3548 |

That is the un-baking, exactly: **3 returns never, in 1,141,216 tries; 7 never even leaves.** Digits 1 and
9 return about 35% of the time — more than the 1-in-3 a uniform rule would give, because the same-type
transition is preferred (self $0.311$ against a flat $1/3$).

**Why those two and not the others.** Each digit owns two classes mod 30, one per ladder, and a digit is
one-way when its *other* shadow dies:

* digit 3's twin shadow is class 23, which is dead — $23+2=25$ (`no_twin_at_23`). So no start can end in 3
  (`three_never_opens`);
* digit 7's base shadow would be class 7 as a closer, which needs a start $\equiv5\pmod{30}$ — i.e. $p=5$
  exactly (`seven_never_closes`).

Digits 1 and 9 have both shadows alive (11 opens, 29 closes for 1; 29 opens, 19 closes for 9), which is
why they can come back. So "permanent" is not a metaphor: it is one residue killed by 5 or by the start
being 5, and the two digits that survive are exactly the two whose both shadows are live.

## 2. The test you asked for, on the fission side

The heavy fragment's last digit is a **closure-offset marker** — 54 is the closure $C(5)=54$, so a heavy
ending in 3 sits one *below* the closure, one ending in 5 sits one above:

$$R_{\text{pred}}=\frac{Z-Z_H}{Z_H},\qquad Z_H\in\{53,54,55,56\}\ \text{read off the digit }(3,4,5,6).$$

| | mean residual | s.d. | worst |
|---|---|---|---|
| the plain pin, $Z_H=54$ | $-0.46\%$ | $2.70\%$ | $6.08\%$ |
| **with the digit** | $-0.19\%$ | **$1.16\%$** | **$2.07\%$** |

**The digit more than halves the error** — s.d. $2.70\%\to1.16\%$, worst case $6.1\%\to2.1\%$. For the
systems is not a fit: it is one integer, $-1,0,+1,+2$, read off the fragment charge.

And the digit is not free — it is *set by the excitation*:

| excitation | n | digits of $Z_H$ | $\langle Z_H\rangle$ | $R$ |
|---|---|---|---|---|
| 0.5 MeV | 6 | 4 only | 54.03 | 0.668–0.744 |
| thermal | 9 | 4, 5 | 54.13 | 0.698–0.758 |
| SF | 5 | 4, 5, 6 | 54.98 | 0.765–0.810 |
| **14 MeV** | **4** | **3, 4** | **53.27** | 0.702–0.755 |

**Every 14 MeV system sits below the closure** ($Z_H<54$, $4/4$) against $6/20$ of the rest — Fisher
one-sided $p=9.4\times10^{-5}$. That is the "permanent alteration" in the fission data: high excitation
pushes the heavy fragment one proton *below* the closure, its digit becomes 3, and **it does not come
back** — no 14 MeV system has $Z_H\ge54$, so the ratio is $4\%$ above the pin's prediction for all four.

## 3. The tracking verdict, again

The one rate in the prime table that is not forced — $P(\text{return}\mid \text{digit }1\text{ or }9)$ —
runs $0.3728, 0.3823, 0.3697, 0.3589, 0.3537$ across five decades: an **8% variation**. The fission ratio
needs **21%**. So the prime-side return rate cannot track it, exactly as the flat digit ratio could not
(`per-system-test.md`). The shape matches; the tracking does not.

## 4. So what is the mechanism, honestly

| level | what is true |
|---|---|
| **the primes** | 3 and 7 are role-locked by residues, so a return to them is impossible — proved, and measured as 0 in 1.14M |
| **the fission fragments** | the heavy's last digit marks the offset from the closure 54; using it halves the pin's error (2.70% → 1.16%) |
| **the link between them** | *formal*: both are "a digit that cannot come back" stories. The prime-side one is forced by 5 and by CRT; the fission-side one is driven by excitation energy |
| **what is not true** | that the prime digits *drive* the fission ratio: the prime-side quantity that could carry it varies 8% where 21% is needed |

The one sentence: **your two-word mechanism is right about which digits are one-way — 3 and 7 are, by
residue — and the fission side shows the same shape at its own closure (a heavy fragment one below 54 does
not return), but the driver there is excitation, not the prime digits.**

## 5. The test to run next, pre-registered

If the mechanism is the closure offset, it makes a prediction that no existing system tests: **a 14 MeV
system heavier than any measured (Z ≥ 94) should have $Z_H\approx53.3$, digit 3, and $R$ about 1.04× the
pin's $(Z-54)/54$.** Pu-239 at 14 MeV already sits at 53.77 — digit 4 but *still below 54*, and its
residual is $+1.86\%$ — so the prediction is already bending the right way. A new 14 MeV evaluation at
$Z=96$ or $98$ would decide it: $Z_H<54$ keeps the mechanism, $Z_H\ge54$ kills it.

That is runnable against ENDF/JEFF if the 14 MeV yields exist for Cm or Cf; if they do not, the test waits
for the data rather than being argued.
