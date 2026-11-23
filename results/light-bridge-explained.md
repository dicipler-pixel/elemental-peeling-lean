# The Light Bridge, explained: how it works, and what it says about temperature, mass, acceleration and energy

A description for a reader who wants the whole thing in one place, with one worked example at the end.
The formal statement is [`master-theorem.md`](master-theorem.md) (proved in `master-theorem.lean`), the
inventory of claims is [`key-correlations.md`](key-correlations.md), and the paper is
[`light-bridge-paper.md`](light-bridge-paper.md).

## 1. The object, in one move

The table is a ladder of **closures** — the counts at which a shell closes:

$$C=(2,10,18,36,54,86,118),\qquad L(m)=2\Bigl\lceil\frac{m+1}{2}\Bigr\rceil^{2},\qquad
W(q)=2\Bigl\lceil\frac q2\Bigr\rceil^{2}.$$

Place a count $Z\le118$ by one coordinate: **how far it still is from the closure of its period**,

$$h=C(m)-Z\ \ (\text{the countdown}),\qquad v=Z-C(m-1)\ \ (\text{what is counted}),\qquad v+h=L(m).$$

That is the whole placement. $h$ is not a decoration: it is simultaneously the **block label**
($h\le5$ p, 6–15 d, 16–29 f, $h=L-2,L-1$ s), the **number of holes** left in the period, and — this is
the part that took measurement — the coordinate along which electronegativity falls (within a block,
$\rho=-0.67$ to $-0.92$) and along which the heat capacity does *not* move ($\rho=+0.02$, $-0.07$).

## 2. Why it works: one identity, and what it forces

The organising identity is

$$W(q)=L(q-1),$$

the rung width at $q$ is the period length at $q-1$ — one function at two arguments. Everything else in
part (A) follows from it and from $L(m)=2n^2$:

* **every capacity is even** ($2n^2$, $2(2l+1)$), so no odd digit can ever label one — which is why the
  prime alphabet $\{1,3,7,9\}$ and the capacity alphabet $\{0,2,4,6,8\}$ are disjoint by necessity;
* the **closures are the partial sums** of the $L$'s ($2, 8, 8, 18, 18, 32, 32 \to 2,10,18,36,54,86,118$);
* the rungs to $q=8$ hold 120 slots, so **two are never filled** ($8s^2$) and the table is **saturated**:
  every $Z\le118$ already has a cell. There is no free cell for a nucleus to step into, which is why a
  descent through the table has to be a **split**.

## 3. The four channels, and the one equation each

| channel | the equation | what it prices | status |
|---|---|---|---|
| **count** | $P=B+K+2$; $p_N-p_1=(2C_2)^{-1}\sum\log^2p_i$ | how many, and how far | proved / 0.022% |
| **prime** | $\langle\text{gap}\rangle=t^2/(2C_2)$, $1/(2C_2)=0.75739$ | the gap between twin starts | measured, 0.001% |
| **fission** | $Z_L+Z_H=Z$, $Z_H\to54=C(5)$ | where the two pieces land | proved arithmetic + measured pin |
| **heat** | $C=3R$ per mole; $\kappa=(1/(2C_2))/3R$ | energy per kelvin, and the exchange | measured / conversion |

**Temperature.** Three different temperatures live in the record and they must not be confused.
(i) The **exchange temperature** $T=\kappa\,t^2$ with $\kappa=0.030364$ K per unit $\log^2p$: a conversion,
fixed by the two coefficients (`conversion_is_forced`), useful for putting a prime-side number on a
thermometer and nothing more. (ii) The **lattice temperature** behind the heat deficit: $C/3R=1$ is the
classical solid, and everything below it is a Debye/Einstein shortfall — measured, labelled H6a–H6d
(7 quantum, 56 classical, 10 soft, 5 weakly off). (iii) The **nuclear temperature**, which is ordinal
only: the charge dispersion at fixed mass gives $\sigma_Z\propto\sqrt T$, so the record reports *ratios*
of temperatures (1.19–1.32) and refuses absolute ones.

**Mass.** The element side has one measured line, $M(Z)=2.619\,Z-9.36$ u ($R^2=0.9985$), from which
$c_{\rm gram}=3R/M$ follows with $r=0.9955$ — per gram, the heat capacity is a prediction from the mass
column. Per *mole* it is the constant $3R=24.943$ J mol⁻¹K⁻¹. The mass that energy needs, though, is not
$M$ but the **mass excess** $\Delta$: in fission the defect is 200 MeV against 219 GeV, one part in a
thousand, and that part *is* the energy.

**Acceleration.** On the prime side the chain moves with a fixed rate in the $(\log p,\text{span})$ plane.
One handoff is $E=\tfrac12 a t^2$ with $a=1/C_2=1.51478$, so $dE/dt=at$ and $d^2E/dt^2=a$ — but the
honest form is discrete and exactly provable: the **second difference** of $\tfrac12at^2$ is $a h^2$, and
its first difference is $at+ah/2$ (`const_accel_second_difference`, `velocity_is_linear`). "Constant
acceleration" here is a statement about a parabola in $\log p$, one handoff at a time, not a dynamics.

**Energy.** Two energies, and the table carries neither directly.
(i) The **span**: $E=\text{span}=(2C_2)^{-1}\sum\log^2p_i=c\,m\,\Delta T$ with $c=1/(2C_2)$ and
$\Delta T=\langle\log^2p\rangle$ — proved given the measured law, 0.022% at $10^9$.
(ii) The **nuclear energy**: $E^*=aT^2$ with $a=A/K$, $K\approx8$–11 MeV — an input, not measured here.
And the theorem that keeps them apart: a mass law linear in $Z$ prices **every** split at its intercept
(`linear_mass_law_blind`), $9.36$ u $=8.72$ GeV for a 200 MeV process, 44× too large and independent of
the split point. Energy needs the mass excess; no count produces it.

## 4. A worked example, both sides

### The prime side: the window $347\le p\le 857$

The fourteen twin starts in that window are $347, 419, 431, 461, 521, 569, 599, 617, 641, 659, 809, 821,
827, 857$ — thirteen handoffs, span **510** (this is the record's own sheet). Then:

| step | computation | value |
|---|---|---|
| the airs | $q-p-2$ down the chain | $70,10,28,58,46,28,16,22,16,148,10,4,28$ |
| check 1 | every air $\equiv4\pmod6$ | ✓ (all thirteen) |
| check 2 | $\sum\text{air}=\text{span}-2m$ | $484=510-26$ ✓ |
| mean gap | $(\text{span})/m$ | $39.2$ |
| $S/V$ | $4/\langle\text{air}\rangle$ | $0.107$ — kindling-ish (segments: 2) |
| **span law** | $\sum\log^2p/(2C_2)$ | $406.7$ against 510 — **20% low** |
| temperature equivalent | $\kappa\langle\log^2p\rangle$ | $0.030364\times41.30=1.25$ K |

And the two merged segments, with their classes from the gap digits alone:

* $419\to431$: one internal air 10, $k=2$ → class $(4+\operatorname{cls}(0))=4+10=14$;
* $809\to827$: airs $10,4$, $k=3$ → class $(6+10+4)=20$.

**Read the span-law line honestly.** At $m=13$ the law is 20% off, because it prices a *mean* and the
window is tiny; at $10^9$ with $m=3.4\times10^6$ it is 0.022% off. That is the same law, at two sample
sizes — the small window shows its scatter, the large one its value.

### The element side: U-235

| step | computation | value |
|---|---|---|
| place it | $m=7$ (since $86<92\le118$), $h=118-92=26$, $v=6$ | f block, 26 holes |
| the pin | $Z_H=C(5)=54$, $Z_L=92-54=38$ | measured $\langle Z_H\rangle=53.98$ ✓ |
| is the light piece closed? | $h(38)=54-38=16=L(5)-2$ | **yes** — a row head |
| the ratio | $Z_L/Z_H=38/54$ | $0.7037$ (measured 0.703) |
| molar heat | $3R$ | $24.943$ J mol⁻¹K⁻¹ |
| measured heat | $C/(3R)$ for U | $1.109$ — label H6d, "weakly off" |
| per gram | $3R/235.04$ | $0.106$ J g⁻¹K⁻¹ |
| the energy | a linear mass law | $8.72$ GeV for every split — 44× too big |
| the real energy | the mass excess | $200$ MeV, not a count |

**The two checkable statements in that table** are the pin ($54$ is the closure, $h(54)=0$) and the
closed test ($h(38)=16=L-2$). Both are proved arithmetic; the $\langle Z_H\rangle=53.98$ beside them is
the measurement that makes the pin a fact about nuclei rather than about the table.

## 5. What the four kinds of claim look like on this example

| claim | on this example | why |
|---|---|---|
| **proved** | $\sum\text{air}=\text{span}-26$; $h(38)=16$; every air $\equiv4$ | arithmetic |
| **measured** | the span law at $10^9$; the pin 53.98; $\langle\text{gap}\rangle=39.2$ here | has an error bar |
| **conversion** | $1.25$ K from $\log^2p$ | fixed once the coefficients are |
| **identification** | "the closure ladder is Coulomb $2n^2$" | a reading, never a premise |

## 6. What the whole thing is for

It is a machine for keeping two things apart that look alike: an **identity** (the table's arithmetic, which
is exact) and a **measurement** (that the world's periodic table and the world's twin primes are this
table and this ladder, which is not exact). Everything usable in the record comes from that discipline:

* you can *place* an element and get its block, its holes, and a closed/open verdict — proved;
* you can *price* a twin window's span, count and ratio — proved + 0.022%;
* you can *locate* the fission fragments at the closure — proved + measured to 0.09 protons;
* and you cannot get an energy from a count, which is the one thing the record says loudest.
