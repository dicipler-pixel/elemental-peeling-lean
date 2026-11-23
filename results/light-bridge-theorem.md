# The Light Bridge theorem

> **Where this sits now.** The collected statement — this theorem plus the fission channel — is
> [`master-theorem.md`](master-theorem.md), proved in [`master-theorem.lean`](master-theorem.lean)
> (25 theorems). For using the table rather than proving things about it, see
> [`light-bridge-manual.md`](light-bridge-manual.md).

## 0. Definitions

$$L(m)=2\Big\lceil\tfrac{m+1}{2}\Big\rceil^{2}\ \ (2,8,8,18,18,32,32),\qquad
C(m)=\sum_{j\le m}L(j)\ \ (2,10,18,36,54,86,118).$$

A **cell** is a pair $(m,q)$ with $m\le q\le 2m-1$; it carries the subshell $(n,l)=(m,q-m)$ of width
$w(m,q)=2(2(q-m)+1)$. A **rung** is a column $q$; its width is $W(q)=\sum_m w(m,q)$; the number of periods
it bridges is $b(q)=q-\lceil(q+1)/2\rceil+1=\lceil q/2\rceil$. For an element $Z$ in period $m$:

$$h=C(m)-Z\ \ (\text{the countdown}),\qquad v=Z-C(m-1)\ \ (\text{the counted part}).$$

---

## 1. Statement

> **Theorem (Light Bridge).**
>
> **(I) Counting.** $W(q)=2\,b(q)^2$; $\sum_{l<m}2(2l+1)=2m^2$; $\sum_{q}W(q)$ over a rung set is the
> inventory of that set.
>
> **(II) Countdown.** $v+h=L(m)$ for every element, with no exception.
>
> **(III) Capacities are periods.** $8=L(2)=L(3)$, $18=L(4)=L(5)$, $32=L(6)=L(7)$; hence the octet, the
> 18-electron rule and the 32-electron rule are one function at three indices.
>
> **(IV) Valence.** $v_{\rm chem}+h=C_{\rm block}$ with $C_s=L(m)$, $C_p=8$, $C_d=18$, $C_f=32$: **117 of
> 118**, the exception being He (group entry 18, valence 2).
>
> **(V) Dichotomy.** Every capacity is even; every prime residue is odd and coprime to 10; therefore
> $\{1,3,7,9\}$ can never label a capacity.

Parts (I)–(III) and (V) are **proved**, machine-checked in
[`light-bridge-theorems.lean`](light-bridge-theorems.lean) (21 theorems) together with
[`scale-theorems.lean`](scale-theorems.lean) (23) — 44 theorems, 0 `sorry`, axioms at most
`propext`, `Classical.choice`, `Quot.sound`. Part (IV) is measured. The promotions have their own
file, [`promotion-theorems.lean`](promotion-theorems.lean) (27 theorems).

---

## 2. Proofs

**(I)** $\sum_{l<m}2(2l+1)=2m^2$ by induction: the $m$-th term adds $2(2m-1)$ and
$2m^2=2(m-1)^2+4m-2$. A rung collects $l=0..\lceil q/2\rceil-1$, so its width is the same sum at
$m=\lceil q/2\rceil=b(q)$, giving $W=2b^2$. *(Lean: `widths_sum`, `rung_width`.)* The inventory follows:
$2\cdot7+6\cdot6+10\cdot4+14\cdot2=118$ *(Lean: `inventory`)*, and the rungs to $q=8$ give 120
*(Lean: `closures_next`)* — the difference being exactly the single cell $(8,8)$, the $8s$.

**(II)** $v+h=(Z-C(m-1))+(C(m)-Z)=C(m)-C(m-1)=L(m)$. *(Lean: `countdown_identity`, by `ring` — the
identity needs no hypothesis at all.)*

**(III)** $2\lceil(2+1)/2\rceil^2=2\cdot2^2=8$, and the same at $m=4,6$ gives 18, 32. *(Lean:
`capacities_are_periods`, `closures`.)*

**(IV)** Checked on all 118 with $v_{\rm chem}$ = group for $s,p,d$ and the count beyond the closure for
$f$. The two former faults — giving $s$ the octet and $f$ the tabulated valence 3 — are worked out in
[`e2-adjustment.md`](e2-adjustment.md).

**(V)** $2(2l+1)$ and $2n^2$ are even, and no even number is $\equiv1,3,7,9\pmod{10}$. *(Lean:
`capacity_never_odd`, `width_even`, `shell_even`, `width_digit_even`, `shell_digit_even`.)*

---

## 3. The map: which part is mathematics, which is physics, which is measurement

| aspect | content | how it is known |
|---|---|---|
| **mathematics** | (I) counting, (II) countdown, (III) capacities = periods, (V) dichotomy | **proved**, 44 Lean theorems in two files |
| **physics** | the widths and capacities are **derived**: $2l+1$ states × 2 spins, and the Coulomb degeneracy $\sum(2l+1)=n^2$ (see `physics.md`). What remains an input is the **$(n+l,n)$ order** and the measured scales $R,c,G$ | derived, except one ordering rule and three scales |
| **measurement** | the inventory (99/118 Madelung, 19 exchange promotions); the property surfaces | measured, with errors stated |
| **conversion** | the rates that translate one reading into another | conventions and one measured number |

That is the whole of "all aspects": the theorem contributes the mathematics, accepts two physical inputs,
and reports the measurements without pretending to derive them.

---

## 4. The conversions — stated so they can be used

| # | conversion | value | status |
|---|---|---|---|
| K1 | unit | 2 members ≡ 2 electrons | identity |
| K2 | step | $T-\text{air}=4$; $w_{l+1}-w_l=4$ | proved |
| K3 | rise | $\text{air}\equiv4\ (6)$; rung increments 6, 10, 14 | proved |
| K4 | closure | $\varphi(30)=8=2+6=4+4=L(2)$ | proved |
| K5 | energy | $\langle\text{air}\rangle=\tfrac{1}{2C_2}t^2-2 \leftrightarrow 3R\,\Delta T$; **0.03036 K per unit $t^2$** | conversion by definition |
| K6 | density | 7 fillable per 30 integers vs 1 element per integer; **0.2333** | proved / definition |
| K7 | index | the $n$-th element ↔ the $n$-th prime, $p_n\approx n(\ln n+\ln\ln n-1)$ | $-2.7\%$ at $n=118$ |

K5 is the one that makes the table usable across the divide: one constant, fixed by the two laws'
coefficients, exactly as 2.54 cm/inch is fixed by definition.

---

## 5. The predictions that ride on it

| quantity | relation | test |
|---|---|---|
| group | $18-h$ ($p,d$), $L(m)-h$ ($s$) | 89/90, He the convention |
| ligands | $h/2$ ($d$ block) | Cr(CO)₆, Fe(CO)₅, Ni(CO)₄; half-integers at the radicals |
| electronegativity | $f(S,\ \text{phase})$ | $R^2=0.83$; **±0.31 Pauli out of sample** |
| ionisation | $f(S,\ \text{phase})$ | ±17% out of sample |
| mass | $2.619\,Z-9.36$ | $R^2=0.9985$, rms 3.5 u |
| specific heat | $3R/M$ | $r=0.9955$ over 78 elements, no free parameter |
| fission | heavy piece at the closure $C(5)=54$; light piece $=Z-54$ | $53.96\pm0.09$ over 21 systems, Th–Cm (`fission-tests.md`) |
| twin count | $\frac1c\int dp/\log^2p$ | $0.005$–$0.02\%$ over four decades |

---

## 6. What the theorem does not contain

* **the inventory.** That there are 118 cells, and which ones, is Madelung — 99 exact with 19
  exchange promotions. The theorem says how the cells sit; it does not say how many there are.
* **the promotions.** [`promotion-theorems.lean`](promotion-theorems.lean) (27 theorems) separates
  the arithmetic from the fit. Arithmetic: the exchange increment has the closed form `G(k) = k` up to
  the half-fill and `G(k) = k + 1 - cap` after it; its peak is at the half-filled shell (`+4` for $d$,
  `+6` for $f$) and its range is `cap - 2` — 8 and 12 quanta against a rung of 1; every one of the
  nineteen moves an electron at the same rung or the next and never two, and then the shape is forced
  (gap 1 ⟹ `s → d`, gap 0 ⟹ `f → d`); the split is ten and nine. The **fit** is one line: three
  rational rungs `A - Bk` that make `G(k) > A - Bk` reproduce the measured $d$ flip sets —
  `fit_3d`, `fit_4d`, `fit_5d` are machine-checked *as fits*, not derivations. And the $f$ series is
  not a rung: a straddle two electrons apart forces `B > 12`, six times the largest $d$ contraction
  (`f_straddle_forces_B`).
* **the properties.** $EN$, $IE_1$, $M$ are fits with stated errors; only $c=3R/M$ is parameter-free.

## 7. One paragraph

Everything in the table is the function $2\cdot^2$ evaluated at an index: the block widths $2(2l+1)=2\times$
an odd number, the shell capacities $2n^2$, the period lengths $2\lceil(m+1)/2\rceil^2$, the rung widths
$2\lceil q/2\rceil^2$, and the closures their partial sums. The countdown splits each period into what is
counted and what is not, exactly; the block capacities 8, 18, 32 are that same period length wherever the
block closes the period; and the only translation needed between the two readings of the inventory is one
rate, 0.03036 K per unit $\log^2p$, fixed by the two laws' coefficients. The mathematics is proved, the two
physics inputs are named, the measurements carry their errors, and what is left over — the inventory and
the nineteen exchange promotions — is stated as the empirical residue it is.
