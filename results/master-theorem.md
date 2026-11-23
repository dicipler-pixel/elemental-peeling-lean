# The master theorem

One statement for the whole object — the Light Bridge table, both of its channels, and what it can
and cannot price. Parts (A)–(L) are **proved** in [`master-theorem.lean`](master-theorem.lean)
(42 theorems, 0 `sorry`, 0 `axiom`, every axiom report ⊆ {`propext`, `Classical.choice`, `Quot.sound`});
part **(M)** is measured, and is checked against ENDF/B-VIII.0 and against the sieve by
`scripts/fission_verify.py` and `scripts/air_law.py`.

## 0. The object

$$C=(0,2,10,18,36,54,86,118),\qquad L(m)=2\Big\lceil\tfrac{m+1}{2}\Big\rceil^{2},\qquad
W(q)=2\Big\lceil\tfrac q2\Big\rceil^{2},\qquad w_l=2(2l+1).$$

A cell is a count $Z\le118$ with period $m(Z)$ the least period whose closure covers it,

$$v=Z-C(m-1)\ \text{(counted)},\qquad h=C(m)-Z\ \text{(countdown)},\qquad v+h=L(m).$$

Blocks are intervals of the countdown: $p$ is $h\le5$ (containing the closure $h=0$), $d$ is
$6\le h\le15$, $f$ is $16\le h\le29$, $s$ is the row head $h\in\{L-2,L-1\}$. A cell is **closed** when
$h\le5$ or $h\in\{L-2,L-1\}$. A **fission event** replaces one cell by two: $Z_1+Z_2=Z$.

## 1. Statement

> **Theorem (Light Bridge, master).**
>
> **(A) Counting.** $W(q)=L(q-1)$: the rung widths and the period lengths are **one function at two
> arguments**, which is the bridge itself. $\sum_{l<m}w_l=2m^2$, so every block width is twice an odd
> number; $L(2)=8$, $L(4)=18$, $L(6)=32$ — the octet, the 18-electron rule and the 32-electron rule are
> one function at three indices; and the closures are the partial sums of the $L$'s.
>
> **(B) Countdown.** $v+h=L(m)$ on all 118 cells.
>
> **(C) Dichotomy.** Every capacity is even; no cell can be labelled by an odd digit. The prime alphabet
> $\{1,3,7,9\}$ and the capacity alphabet $\{0,2,4,6,8\}$ are disjoint by necessity, not by measurement.
>
> **(D) Split.** For every fission event, $h_1+h_2=C(m_1)+C(m_2)-Z$; if both pieces lie in one period,
> $(v_1+v_2)+(h_1+h_2)=2L(m)$; the count is conserved exactly, $Z-Z_1=Z_2$; a symmetric split needs an
> even parent.
>
> **(E) Pin.** $C(5)=54$, so a heavy piece at 54 sits at $h=0$ — the closure cell, group 18. The light
> piece is $Z-54$, with countdown $108-Z$ while it stays in period 5 ($91\le Z\le108$). With the heavy on
> the closure, the light piece is a closed cell only for $88\le Z\le92$.
>
> **(F) Closed cells.** In the asymmetric window $30\le Z_1\le46$: for $Z=92$ both pieces are closed
> exactly for $Z_1\in\{36,37,38\}$; for $Z=94$ exactly for $Z_1=38$; for $Z=96$ for none.
>
> **(G) Switch.** The symmetric split sits at cell $Z/2$ with countdown $54-Z/2$; for even $Z$ it is
> closed exactly when $Z\ge98$.
>
> **(H) Thorium.** $C(4)+C(5)=36+54=90$; with the heavy on the closure, a light piece also on a closure
> forces $Z=90$.
>
> **(I) Inventory and saturation.** $2\cdot7+6\cdot6+10\cdot4+14\cdot2=118$; the rungs to $q=8$ hold 120,
> so two cells are unfilled (the $8s$); every $Z\le118$ has a period — hence a cell, already taken. There
> is no free cell below the last closure for a nucleus to descend into one at a time, which is why the
> descent is a split rather than a step.
>
> **(J) Energy is outside.** A mass law linear in $Z$ prices every split at its intercept — the linear
> terms cancel — so the table's $M=2.619Z-9.36$ gives $9.36$ u $=8.72$ GeV for a 200 MeV process, and the
> same number for every split point. Energy needs the mass excess, which is not a count.
>
> **(K) The forces.** **(K1)** The closure law is the Coulomb degeneracy: the period lengths are $2n^2$,
> so the table is an **electromagnetic** ladder. **(K2)** The **strong** ladder is the 3D oscillator
> $n(n+1)(n+2)/3$: it agrees with Coulomb at 2 and 8, exceeds it from the third cumulant (18 against 20),
> and meets the observed magic numbers $2,8,20,28,50,82,126$ at 2, 8 and 20 before spin-orbit splitting
> takes over. **(K3)** The fission *mode* is not the force balance — $Z^2/A$ spans 34.91–39.06, a factor
> 1.12, while the measured valley/peak spans 481 — it is ordered within each excitation class by
> $h_{\rm sym}=54-Z/2$, the countdown of the symmetric fragment (Spearman $-0.80$ to $-0.89$), and not by
> the heavy fragment's distance from $N=82$, which reverses sign inside the spontaneous set.
>
> **(L) The zeta zeros.** **(L1)** The trivial zeros are the forced lattice — negative even integers, no
> arithmetic content, the same status as the closure ladder forced by $2n^2$. **(L2)** The non-trivial
> zeros are the fluctuation of the prime count, and the record **measures them**: the explicit formula
> makes $(\psi(x)-x)/\sqrt x$ a sum of cosines in $\log x$ at the zeros' frequencies, with amplitude
> $2/\gamma$; resolving it below $10^7$ returns **twelve of twelve known zeros**, each within 0.35 of a
> 0.68 resolution element, amplitudes following $2/\gamma$ to 2% (correlation 0.9965), and a shuffled
> control recovering 2.3 of 12. The twin count is the exception — a Hardy–Littlewood object with no
> classical explicit formula, so its residual sits *at* the zero bound without resolving one.
> **(L3)** The exact part of the table is the *finite* Euler product ($30=2\cdot3\cdot5$, eight classes,
> 0 exceptions); the zeros are the infinite remainder, some seventy times higher in frequency.
> **(L4)** The one measured prime-side *bias* (end digits, diagonal at 0.15–0.16) decays as $c/\log p$
> with $c\to1.4$, and its main term is the prime-tuple singular series, not the zeros.
>
> **(M) Measured.** the air/gap law $\langle\text{gap}\rangle=t^2/(2C_2)$, flat to $0.001\%$ to $10^{12}$;
> the twin count $2C_2\int dp/\log^2p$ to $0.005\%$; the inventory (99 Madelung + 19 exchange promotions);
> the fission charge pin $\langle Z\rangle_{\rm heavy}=53.96\pm0.09$ over 21 systems; the closed-cell
> shares 0.36 (Th) → 0.16 (U) → 0.000 (Pu and above); the valley series $0.0002\to0.0026\to0.067$ for
> $Z=96,98,100$.

## 2. What each part is for

| part | what you use it for | where the detail lives |
|---|---|---|
| (A) | any counting question: capacities, period lengths, rung widths, the inventory | [`light-bridge-theorem.md`](light-bridge-theorem.md) |
| (B) | to place an element: $h$, $v$, block, group | `chain-table.md` C14–C16 |
| (C) | to rule out a coincidence: an odd capacity cannot exist | [`light-bridge-theorems.lean`](light-bridge-theorems.lean) |
| (D) | to book any fission or decay: what a split conserves and what it costs | [`fission-theorem.md`](fission-theorem.md) |
| (E) | to place a fragment given its partner | §2 of the fission theorem |
| (F) | to test "both pieces on the key" for a given parent | §3 of the fission theorem |
| (G) | to say whether symmetric fission is on a closed cell | `symmetric_closed` |
| (H) | the one nucleus whose two halves are both closures | `fission-tests.md` §4 |
| (I) | why a descent must split | `fission-and-the-key.md` §2 |
| (J) | why the table cannot give an energy | [`mass-temperature-energy.md`](mass-temperature-energy.md) |
| (K) | which force owns which coordinate, and how the mode is ordered | [`strong-force-bolstered.md`](strong-force-bolstered.md) |
| (L) | the zeta zeros: forced, fluctuating, and **found in the primes** | [`zeros-in-the-primes.md`](zeros-in-the-primes.md) |
| (M) | the constants, with error bars | `air-law-offset.md`, `fission-tests.md` |

### The four prime counts

Part (L2) says the *twin* count has no explicit formula. That is a statement about the twin count
only. The other prime-side counts do have one, of three different kinds, and each is written out in
[`count-formulas.md`](count-formulas.md) with its arithmetic in
[`count-formulas.lean`](count-formulas.lean): the base count and the twin-ladder count are **zero
sums** (of $L(s,\chi_{-3})$, whose zeros are found in the primes — 19 of 19 peaks, 25 of 25 zeros),
the twin count is a **telescoping identity** plus a singular series, and the double twin count is a
singular series with no free parameter, $(2C_2)^2\mathrm{Li}_3(x)$, good to 1–2%.

## 3. Proof status, stated separately

```
lean results/master-theorem.lean      # 42 theorems, 0 errors, 0 warnings, no output
grep -c sorry results/master-theorem.lean       # 0
#print axioms <each of the 25>        # ⊆ {propext, Classical.choice, Quot.sound}
```

Random inputs are checked separately and wired into the same command
([`random-tests.md`](random-tests.md)): ten property groups at 20,000 trials each, and a cross-check
that Lean's proved `period`, `cnt`, `counted` and `closed` agree with the reference implementation on
random cells — the one thing a proof cannot notice, that the code and the theorem have drifted apart.

The file defines the table itself — so (A)–(L) are statements about *this* table, and the claim that the
real periodic table *is* this table is the measured content of `light-bridge-theorem.md` (C15, 118
elements, no exceptions). That separation is the same one the audited files carry: **proved** is the
arithmetic; **measured** is that the arithmetic is the world's.

## 4. What the master theorem is not

* not a derivation of the inventory (that is Madelung plus 19 promotions, empirical);
* not a derivation of the constants in (M) — they are measured, with their errors;
* not dynamics: (D)–(H) say where pieces land and what is conserved, never whether a nucleus splits;
* not the neutron side: a $Z$-indexed table cannot see neutrons, and the neutron closure ladder
  (2,8,20,28,50,82,126) shares only the term 2 with the proton one — so (A)–(I) do not transfer
  ([`the-second-coordinate.md`](the-second-coordinate.md)).
