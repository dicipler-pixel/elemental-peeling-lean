# How to use the Light Bridge

A working manual: what goes in, what comes out, which relation to apply in which order, and the checks
that catch an error. Everything here is one of the four kinds of number the record keeps — **proved**,
**measured**, **conversion by definition**, or **fitted** — and each entry says which.

## 1. The four entrances

You arrive at the table with one of four things, and each has its own route in.

| you have | you want | route |
|---|---|---|
| an **element** ($Z$, 1–118) | its cell, block, group, capacity, valence | §2 |
| a **twin pair** $p,p+2$ and the next $q$ | air, total, class, digit, value | §4 |
| a **fission or decay event** | the two cells, the pin, the neutron gap | §5 |
| a **count** ($B$, $K$, $N$, $D$) | its exact formula and what kind of formula it is | §4a |

## 2. From an element to its cell

Four steps, all arithmetic:

1. **Period.** $m$ is the least period with $Z\le C(m)$, using $C=(2,10,18,36,54,86,118)$.
2. **Countdown and counted part.** $h=C(m)-Z$, $v=Z-C(m-1)$. Check $v+h=L(m)$ — it always holds
   (proved on all 118 cells).
3. **Block.** From $h$ alone: $p$ if $h\le5$, $d$ if $6\le h\le15$, $f$ if $16\le h\le29$, $s$ if
   $h=L(m)-2$ or $L(m)-1$.
4. **Group.** $18-h$ for $p$ and $d$; $L(m)-h$ for $s$; the actinide/lanthanide convention for $f$.

Worked:

| element | $m$ | $v$ | $h$ | $L(m)$ | block | group |
|---|---|---|---|---|---|---|
| Ca, $Z=20$ | 4 | 2 | 16 | 18 | $s$ | $18-16=2$ ✔ |
| Fe, $Z=26$ | 4 | 8 | 10 | 18 | $d$ | $18-10=8$ ✔ |
| Xe, $Z=54$ | 5 | 18 | 0 | 18 | $p$ | $18-0=18$ ✔ |
| U, $Z=92$ | 7 | 6 | 26 | 32 | $f$ | actinide |

**The capacity you may quote** is $L(m)$ for the period, and $w_l=2(2l+1)$ for the block — and since
$W(q)=L(q-1)$, the rung width at $q$ is the period length at $q-1$. That identity is the bridge: one
function, two arguments, and it is why the octet, the 18- and the 32-electron rule are $L(2),L(4),L(6)$.

## 3. The distance-to-closure reading (her "countdown")

$h$ is how far the element still is from the close of its period, and it is the most useful single
number in the table, because the chemistry follows it: mean Pauling electronegativity falls
$2.60\to0.96$ as $h$ runs $0\to7$ (Spearman $-0.92$ against $-0.36$ for the period). So: **to compare two
elements, compare $h$ first, period second.**

## 4. From a twin pair to its key

Given consecutive twin starts $p<q$ (both $p$ and $p+2$ prime):

1. **Air** $=q-p-2$, the gap between the pairs. It satisfies air $\equiv4\pmod 6$ — always
   (proved), so air mod 30 ∈ $\{4,10,16,22,28\}$.
2. **Total** $T=\text{air}+4$; class $T\equiv$ class(air)$+4\pmod{30}$, i.e. $T\bmod30\in\{8,14,20,26,2\}$.
3. **Class $\leftrightarrow$ digit** is a bijection: air 4,10,16,22,28 ↔ digit 4,0,6,2,8.
4. **Value ladder** $V=\tfrac34g+\tfrac12 \pmod{7.5}$ on the gap residue: $4\to3.5$, $10\to8$, $16\to5$,
   $22\to2$, $28\to6.5$; and $V(T)=V(\text{air})+3$ always.

Worked, $(11,13)\to(17,19)$: air $=4$, class 4, digit 4, $T=8$, $V=3.5$. The next pair gives
$V=6.5=3.5+3$ ✔ — the $+4$ shift in the class is a $+3$ shift on the ladder.

**The law on the air** (measured): $\langle\text{gap}\rangle=t^2/(2C_2)$, i.e.
$\langle\text{air}\rangle=t^2/(2C_2)-2$ with $t=\log p$ and $1/(2C_2)=0.757390$. Flat to $0.001\%$ to
$10^{12}$; the offset is the half-pair, not a fudge. **Do not** use $\tfrac34$ as the coefficient — that
reading is dead at $254\sigma$.

## 4a. From a count to its formula

Four counts, three kinds of formula. Which kind is available is decided by what the count is, not by
effort — the detail is [`count-formulas.md`](count-formulas.md), the arithmetic
[`count-formulas.lean`](count-formulas.lean).

| count | definition | the exact formula | kind |
|---|---|---|---|
| base $B(x)$ | $p\equiv1\ (6)$, the $4+6k$ ladder | $\psi(x;6,1)-\psi(x;6,5)=-\sum_\rho x^\rho/\rho$, $\rho$ over $L(s,\chi_{-3})$ | **zero sum** — and its zeros are found in the primes (19/19 peaks) |
| twin ladder $K(x)$ | $p\equiv5\ (6)$ | the same, one sign flipped | **zero sum** |
| twin $N(x)$ | $p,p+2$ prime | $\sum\text{air}=\text{span}-2\hat N$, and $N=2C_2\mathrm{Li}_2$ | **telescoping** + singular series |
| double twin $D(x)$ | a handoff with nothing between partner and next start | consecutive primes $r<s$ with $r-2$, $s+2$ prime; $D=(2C_2)^2\mathrm{Li}_3$ | **singular series** |

The twin count has no zero sum and cannot have one: $\mathbf 1_{p,\,p+2}$ is a condition on a tuple,
not on a residue, so there is no multiplicative weight and no $L$-function. Every relation is R18–R28
in §6.

## 4b. From a heat capacity to its label

Nine labels, H1–H9, in [`specific-heat-bridge.md`](specific-heat-bridge.md) §2, with the arithmetic in
[`specific-heat.lean`](specific-heat.lean). The two that decide questions:

* **H1 vs H2/H3** — a Light Bridge *capacity* is a count of slots (even: $L(m)=2n^2$); a *heat capacity*
  is an energy per kelvin. `three_not_a_capacity`: $2(2l+1)\ne3$ for every $l$, so the Dulong–Petit 3 can
  never label a cell. Different objects, one word.
* **H7** — the only exchange, $\kappa=1/(2C_2)\big/3R=0.030364$ K per unit $\log^2p$, and it is *forced*
  by the two coefficients: `conversion_is_forced`. Nothing was fitted.

And the measurement that stops a false claim: $\mathrm{Spearman}(C/3R,h)=+0.57$ over 78 elements but
$+0.02$ in the p block and $-0.07$ in the d block — **the countdown does not order the heat**; the overall
correlation is the composition of blocks.

## 5. From an event to two cells

For a split $Z_1+Z_2=Z$:

1. **Bookkeeping.** $h_1+h_2=C(m_1)+C(m_2)-Z$; if both pieces are in one period,
   $(v_1+v_2)+(h_1+h_2)=2L(m)$.
2. **The pin.** The heavy piece sits at $C(5)=54$ ($h=0$, group 18) across Th–Cm; the light piece is
   $Z-54$ with countdown $108-Z$.
3. **The closed test.** A piece is *closed* if $h\le5$ or $h\in\{L-2,L-1\}$. Both closed happens for
   $Z_1\in\{36,37,38\}$ at $Z=92$, only $38$ at $Z=94$, and never at $Z=96$.
4. **The symmetric switch.** The symmetric split is at cell $Z/2$; it is closed iff $Z\ge98$.
5. **The neutrons.** $\nu=A-(A_1+A_2)$ — the mass balance, which the table cannot see but the yields give.

Worked pair: U-235 → 38 + 54. $h(38)=16=L(5)-2$ (row head, closed) and $h(54)=0$ (closure, closed);
$v_1+v_2=2+18=20$, $h_1+h_2=16$, total $36=2L(5)$ ✔. Thorium → 36 + 54: $36=C(4)$ and $54=C(5)$, so
both are closures and $C(4)+C(5)=90=Z$ ✔.

## 6. The relation list, with status

| # | relation | use it for | status |
|---|---|---|---|
| R1 | $v+h=L(m)$ | place any element; catch a slip | **proved** (118 cells) |
| R2 | $W(q)=L(q-1)$ | rung width from period length | **proved** |
| R3 | $\sum_{l<m}w_l=2m^2$; $w_l=2(2l+1)$ | capacity, parity | **proved** |
| R4 | $L(2),L(4),L(6)=8,18,32$ | the three shell rules | **proved** |
| R5 | closures = partial sums of $L$ | the closure ladder | **proved** |
| R6 | air $\equiv4\ (6)$; $T=\text{air}+4$ | prime classes | **proved** |
| R7 | class $\leftrightarrow$ digit bijection | read a class off a digit | **proved** |
| R8 | $V(T)=V(\text{air})+3$ | move between the two keys | **proved** (arithmetic of the ladder) |
| R9 | $\langle\text{gap}\rangle=t^2/(2C_2)$ | the prime-side law | **measured**, $0.001\%$ |
| R10 | $N(x)=2C_2\int dp/\log^2p$ | twin counting | **measured**, $0.005\%$ |
| R11 | $h_1+h_2=C_1+C_2-Z$; $Z_1+Z_2=Z$ | any split | **proved** |
| R12 | heavy at $C(5)$, light $=Z-54$ | fission fragments | **measured**, $53.96\pm0.09$ |
| R13 | closed-cell splits $\{36,37,38\}$ at 92 | the "both legal" test | **proved** |
| R14 | symmetric closed iff $Z\ge98$ | the mode switch | **proved** |
| R15 | $\nu=A-A_1-A_2$ | neutrons from masses | **measured** (2.4–4.1) |
| R16 | $c=3R/M$ | solid-side heat capacity | **measured**, $r=0.9955$ |
| R17 | $\kappa=c/3R=0.03036$ K per unit $t^2$ | convert the two sides | conversion by definition |
| R18 | $P=B+K+2$ | the two ladders are one count | **proved** |
| R19 | twin start $>3\Rightarrow p\equiv5\ (6)$; $N\le K+1$ | twins sit on one ladder | **proved** |
| R20 | twin start $>5\Rightarrow p\equiv11,17,29\ (30)$ | the twin key's three types | **proved** |
| R21 | air $\equiv4\ (6)$, $T=\text{air}+4\equiv2\ (6)$ | which alphabet | **proved** |
| R22 | quadruplet $\Rightarrow p\equiv11\ (30)$ | the minimal merge's class | **proved** |
| R23 | $\sum\text{air}=\text{span}-2\hat N$ | count = span ÷ mean gap | **proved** |
| R24 | $B-K=-\sum_\rho x^\rho/\rho$ over $L(s,\chi_{-3})$ | the split as a zero sum | **proved** form, **measured** spectrum |
| R25 | $N=2C_2\mathrm{Li}_2$ | the twin count | **measured**, 0.02% |
| R26 | $D=(2C_2)^2\mathrm{Li}_3$ | the double twin count | **measured**, 1–2% |
| R27 | $D/\hat N=2C_2/\log x$ | the merge rate | **measured**, 0.5% per decade |
| R28 | segments $=\hat N-D+1$; sizes cluster | how pairs group | **measured** |
| R29 | $D=M/V$, $C=c\cdot M=c\cdot D\cdot V$ | the density triangle and its heat twin | **proved** (`Heat.triangle_all`, `Heat.heat_triangle`) |
| R30 | $\rho c=C/V_m=3R/V_m$ | the volumetric heat capacity | **proved**; unmeasured (§4 of `specific-heat-bridge.md`) |
| R31 | $C=3R\Leftrightarrow C/3R=1$; labels H6a–H6d | which solid is classical | **proved** iff, **measured** labels |
| R32 | $3\notin$ capacities; $2(2l+1)\neq3$ | why $3R$'s 3 cannot label a cell | **proved** |
| R33 | $\kappa=a/3R=0.030364$, forced | convert the two sides | conversion by definition, no free parameter |
| R35 | the four digits: two classes each, openers 1/7/9, closers 1/3/9, class 23 dead | build the Light Table | **proved** ([`digit-table.md`](digit-table.md)) |
| R34 | $p_N-p_1=(2C_2)^{-1}\sum\log^{2}p_i$ | span from the list, count from a span, mean gap from both | **proved** given the measured constant; 0.022% at $10^{9}$ ([`one-equation.md`](one-equation.md)) |

## 7. The checks that catch an error

Run these after any calculation. Each is exact:

* $v+h=L(m)$ — if it fails, the period is wrong.
* air $\equiv4\pmod 6$ — if it fails, you are not looking at a twin handoff.
* every capacity even — if an odd number appears as a capacity, the arithmetic is wrong, not the table.
* $Z_1+Z_2=Z$ — protons are conserved with no correction; a nonzero residual means neutron **number**
  confusion ($A$ vs $Z$).
* $\nu\ge0$ and $\sum A+\nu=A_{\rm parent}$.

## 8. What not to use it for

* **An energy.** The table's mass law is linear in $Z$, and a linear mass law prices every split the same
  ($8.72$ GeV for a 200 MeV process, whatever the split). Energy needs the mass excess.
* **A neutron count as a cell.** The table is $Z$-indexed; capture, elastic scattering and excitation are
  all invisible. If you need them, index by $(Z,N)$ — and then the closure ladder changes to the magic
  numbers, which share only the term $2$ with the proton one.
* **A residue key on the element side.** $Z$ is a count; capacities are even; the end digit is a
  capacity label, not a residue.
* **The inventory as a theorem.** 118 cells with 19 exchange promotions is Madelung plus measurement —
  the theorem says how cells sit, not how many there are.

## 9. One-page recipe

```
ELEMENT Z:   m = least period with Z <= C(m);  h = C(m) - Z;  v = Z - C(m-1);  check v+h = L(m)
             block from h (p<=5, d 6-15, f 16-29, s L-2,L-1);  group = 18-h (p,d), L-h (s)
PRIMES p,q:  air = q-p-2 (≡4 mod 6);  T = air+4;  class = air mod 30;  digit = air mod 10;
             V(air) = 3/4 air + 1/2 mod 7.5;  V(T) = V(air)+3
SPLIT Z:     Z1+Z2 = Z;  h1+h2 = C1+C2-Z;  heavy at 54;  light = Z-54;  h_light = 108-Z
             closed = (h<=5) or (h in {L-2,L-1});  symmetric closed iff Z>=98
LAWS:        <gap> = t^2/(2C2);  N = 2C2 ∫dp/log^2 p;  nu = A - A1 - A2
COUNTS:      P = B+K+2;  N <= K+1;  D = (2C2)^2 ∫dp/log^3 p;  B-K is a zero sum (L(s,chi_-3))
             sum air = span - 2*handoffs   (count = span / mean total gap)
```
