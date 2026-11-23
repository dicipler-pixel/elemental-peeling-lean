# The two-ladder scale: statement, proof, and every facet

> **Superseded as the statement of the theorem.** This is the older framing: two ladders, side by side.
> The statement that replaced it puts everything on **one axis** — the closure — in
> [`light-bridge-theorem.md`](light-bridge-theorem.md), and that is the file to read first. The numbers
> here are unchanged and still valid; what is superseded is the *split into two ladders*, not any
> measurement. Keep this file for two things the newer one does not carry: the four-cube of §0, and the
> prime-ladder detail of §1(i).

## 0. The frame — the four-cube and the corner that is a constant

A quantity carries four exponents, $(a,b,c,d)$ on $L^aT^bM^c\Theta^d$ — the sixteen corners of the
four-cube. Specific heat sits at

$$[c]=\frac{[E]}{[M][\Theta]}=L^2T^{-2}\Theta^{-1}\quad\Longrightarrow\quad(a,b,c,d)=(2,-2,0,-1),$$

and the one fact this work adds to that cube is that **this corner is a constant**: for every solid
element, $C_{\rm molar}=3R=24.94\ \mathrm{J\,mol^{-1}K^{-1}}$ — Dulong–Petit. The corner whose value
does *not* depend on which element you are looking at.

The same form appears on the prime ladder with a different intensive measure:

$$c=\frac{E}{m\,\Delta T}\ \longleftrightarrow\ c=\frac{(\sum\text{air})+2m}{m\,\langle t^2\rangle}=\frac{1}{2C_2}=0.75739,$$

energy per segment per unit of $\log^2p$ instead of per kelvin. The theorem below is about that shared
form and about what each ladder's counting forces.

---

## 1. Statement

> **Theorem (two-ladder scale).** Let the *prime ladder* be the twin starts $p\equiv11,17,29\pmod{30}$
> with air $=q-p-2$ and total $T=q+2-p$ between consecutive pairs, and let the *element ladder* be the
> fill order $(n+l,n)$ with block widths $w_l=2(2l+1)$, rung widths $W(q)=\sum_{l<\lceil q/2\rceil}w_l$
> and depths $d_l$.
>
> **(i) Prime ladder, exact.** $\text{air}\equiv4\pmod 6$, so $\text{air}\bmod30\in\{4,10,16,22,28\}$;
> class $\mapsto$ end digit is a **bijection**; $T=\text{air}+4$ shifts the class by 4; a gap
> $\equiv2\pmod6$ is never followed by a gap of 2; a 30-row holds at most 7 primes; no column of the
> prime table carries a run of more than 5.
>
> **(ii) Element ladder, exact.** $W(q)=2\lceil q/2\rceil^2$; $\sum_{l<m}w_l=2m^2$; the depth vector at
> the end of period $m$ is $d_0=m$, $d_l=m-2l+1$; $N(m)=\sum_l w_ld_l$ gives $N(7)=118$, $N(8)=168$,
> $N(9)=218$.
>
> **(iii) Dichotomy, exact.** Every capacity in (ii) is **even**; every prime residue in (i) is **odd**
> and coprime to 10. Hence $\{1,3,7,9\}$ and $\{0,2,4,6,8\}$ are disjoint by necessity — the first
> alphabet labels units, the second labels the space between units.
>
> **(iv) Laws, measured.** $\langle\text{air}\rangle=\tfrac{1}{2C_2}t^2-2$, i.e.
> $\langle\text{gap}\rangle=\tfrac{1}{2C_2}t^2$ with no offset (flat to $0.05\%$ over four decades to
> $10^{11}$ — `air-law-offset.md`; the $3/4$ reading of earlier versions is falsified at $78\sigma$);
> $C_{\rm molar}=3R$ (72% of elements within 10%); $c_{\rm gram}=3R/M$ ($r=0.9955$); $M=2.62Z-9.4$
> ($R^2=0.9985$); $EN=1.52+0.102g-0.169m$ ($R^2=0.83$).

Parts (i)–(iii) are **machine-checked**: [`scale-theorems.lean`](scale-theorems.lean), 23 theorems,
0 `sorry`, axioms exactly `propext`, `Classical.choice`, `Quot.sound`. Part (iv) is measurement and is
reported as such. What the Lean covers, and where its object is still only arithmetic, is audited
declaration by declaration in [`lean-audit.md`](lean-audit.md).

---

## 2. Proof of (i) — the prime ladder

**Step 1.** A twin start is one of $11,17,29\pmod{30}$, and this is *derived*, not assumed: if $p$ and
$p+2$ are primes above 5 then $3\nmid p$ and $3\nmid p+2$ (else $p=3$ or $p+2=3$), so $p\equiv2\pmod3$;
$5\nmid p$ and $5\nmid p+2$ likewise, which excludes the class 23; with $p$ odd the remaining classes mod
30 are 11, 17, 29. *(Lean: `twin_class`, via `prime_mod3`, `Nat.dvd_prime`, `omega`; the residue-only
form is `class_mod3`.)*

**Step 2.** Both endpoints are odd primes and both are $\equiv2\pmod3$, so $q-p$ is even and divisible
by 3, hence divisible by 6. *(Lean: `twin_gap_mod6`.)*

**Step 3.** Therefore $\text{air}=q-p-2\equiv4\pmod6$. *(Lean: `air_mod6`.)*

**Step 4.** A number $\equiv4\pmod6$, reduced mod 30, is one of $4,10,16,22,28$ — five classes, because
$4+6k$ for $k=0..4$ and $6\cdot5=30$. *(Lean: `air_five_classes`.)*

**Step 5.** Those five classes have five distinct residues mod 10, so the class determines the end digit
and conversely: the map is injective, hence a bijection on five elements. *(Lean: `class_digit_inj`;
the digit table itself is `class-digit-table.md`.)*

**Step 6.** $T=\text{air}+4$ adds the pair, so $T\bmod30\in\{8,14,20,26,32\}$: the twin key's classes are
the base key's shifted by the pair width. *(Lean: `total_class`, one representative; the other
four are the same computation.)*

**Step 7 — the carry.** If $p\equiv2\pmod3$ then $p+4\equiv0\pmod3$, so the prime after $p$ cannot be
$p+4$; a gap of 2 therefore cannot be followed by a gap of 2. *(Lean: `carry_mod3`.)*

**Step 8 — capacity 7.** In any 30-block the eight admissible classes are $30k+r$ with $r$ ranging over
the units mod 30; mod 7 these become $2k+\{0,1,2,3,4,5,6\}$, so one of the eight is divisible by 7 and is
therefore composite unless it equals 7. *(Lean: `row_capacity_seven`.)*

**Step 9 — runs.** Among any seven consecutive terms of a progression of step 30, one is divisible by 7:
$30\equiv2\pmod7$, and $2^{-1}\equiv4$, so the term at index $i\equiv-4a\pmod7$ is the multiple. A run of six gaps of 2 would be seven such
terms, and the only progression of that shape containing 7 is $7,\dots,187$, which fails at
$187=11\cdot17$. So the longest run of 1s is 5, attained at $7,37,67,97,127,157$. *(Lean:
`run_bound`; the arithmetic $187=11\cdot17$ is `norm_num`.)*

---

## 3. Proof of (ii) — the element ladder

**Widths.** $\sum_{l<m}2(2l+1)=2m^2$ by induction: the $m$-th term adds $2(2m-1)$ and
$2m^2=2(m-1)^2+4m-2$. *(Lean: `widths_sum`.)*

**Rungs.** A rung $q=n+l$ collects $l=0..\lceil q/2\rceil-1$, so its width is the same sum with
$m=\lceil q/2\rceil$, giving $W(q)=2\lceil q/2\rceil^2$. *(Lean: `rung_width`.)*

**Depths.** At the end of period $m$ the $s$-block holds the $m$ shells $1s..ms$ and each other block
holds one fewer per step of two in $l$: $d_l=m-2l+1$ for $l\ge1$, clamped at 0. Substituting,
$N(m)=\sum_l w_ld_l$ gives 118, 168, 218 for $m=7,8,9$. *(Lean: `inventory`, `closures_next`;
the depth vectors are computed in `chain-table.md`.)*

**The measured part of (ii)** — that these widths are *what the elements use* — is the 118 count:
$2\cdot7+6\cdot6+10\cdot4+14\cdot2=118$, and the block/h-interval table, both checked on all 118
elements and reported in `chain-table.md` §2 and §6.

---

## 4. Proof of (iii) — the dichotomy

$w_l=2(2l+1)$ is even and $2n^2$ is even, so every capacity is even; and a number that is even cannot be
$\equiv1,3,7,9\pmod{10}$, which are exactly the residues coprime to 10 that an odd prime can take.
*(Lean: `capacity_never_odd`, `width_even`, `shell_even`, `width_digit_even`.)*

The consequence is physical, not statistical: a neutral atom with an odd electron count has a
half-integer total spin, so **every one of the 59 odd-$Z$ elements is paramagnetic as a free atom**. The
measured check is that the digit carries nothing beyond parity (Spearman $+0.059$, $p=0.61$ against the
Dulong–Petit residual), so the digit's whole content is the parity that (iii) gives it a priori.

---

## 5. Every facet on one scale

Each row is (observable) = (universal constant) × (scale factor). The constant is what the ladder fixes;
the factor is what varies.

| facet | observable | law | value / fit | status |
|---|---|---|---|---|
| prime class | air mod 30 | five classes | $\{4,10,16,22,28\}$ | **proved** |
| class = digit | air mod 10 | bijection | 5 ↔ 5 | **proved** |
| twin total | $T$ | class + 4 | $\{8,14,20,26,32\}$ | **proved** |
| carry | gap ≡ 2 mod 6 | next ≠ 2 | 0 exceptions /14.1M | **proved** |
| row capacity | primes per 30 | 7 | attained | **proved** |
| run bound | run of 1s | 5 | attained at 7 | **proved** |
| air law | $\langle\text{air}\rangle$ | $c\,t^2-2$ | $c=1/(2C_2)=0.75739$ | measured, 0.05% flat |
| twin count | $N(x)$ | $\frac1c\int\frac{dp}{\log^2p}$ | 0.005–0.02% | measured, no free parameter |
| block width | $w_l$ | $2(2l+1)$ | 2,6,10,14,18 | **proved** |
| rung width | $W(q)$ | $2\lceil q/2\rceil^2$ | 2,2,8,8,18,18,32,32,50 | **proved** |
| shell | $\sum_{l<n}w_l$ | $2n^2$ | 2,8,18,32 | **proved** |
| depth | $d_l$ | $m-2l+1$ | 7,6,4,2 (m=7) | **proved** |
| inventory | $N(m)$ | $\sum w_ld_l$ | 118, 168, 218 | **proved** |
| blocks | $h$-intervals | 6,10,14,2 | all 118 | measured |
| group | $18-h$ | one line | 89/90 | measured |
| rung vs period | $q$ | $m$ or $m+1$ | all 118 | measured |
| exceptions | rule failures | exchange step $G(k)$ | 19, 30/30 d-block | fitted |
| electronegativity | EN | $1.52+0.102g-0.169m$ | $R^2=0.83$ | fitted |
| ionisation | $IE_1$ | $1239+26.7g-155m$ | $R^2=0.51$ | fitted |
| radius | $\langle r\rangle$ | grows with $m$ | 72→183 pm | measured |
| mass | $M$ | $2.62Z-9.4$ | $R^2=0.9985$ | fitted |
| molar heat | $C$ | $3R$ | 72% within 10% | law |
| specific heat | $c=C/M$ | $3R/M$ | $r=0.9955$ | law |
| digits | capacities | even | $\{0,2,4,6,8\}$ | **proved** |
| spin | $Z$ odd | half-integer | 59 elements | theorem |

Twenty-five facets, three kinds: **proved** (the residue skeleton and the counting), **law** (the two
universal constants, $3R$ and $1/(2C_2)=0.7574$ with its forced offset $-2$), **fitted or measured**
(the property surfaces).

---

## 6. What is not proved, and what would break the theorem

* **(iv) is measurement.** $1/(2C_2)$ is a measured coefficient with a *forced* offset $-2$ (the
  half-pair), not a fitted pair of numbers: the offset is geometric and the coefficient is one number,
  $0.75739$, flat to $0.05\%$ from $10^7$ to $10^{11}$. The earlier $3/4$ reading is falsified —
  `air-law-offset.md`.
* **The element ladder's 19 exchange promotions**: the arithmetic is proved
  ([`promotion-theorems.lean`](promotion-theorems.lean), 27 theorems), the fit is two numbers per $d$
  series, and the $f$ series admits no linear rung at all.
* **The five odd digits**: the theorem says the four prime digits cannot label a capacity. It does not
  say why the *fifth* odd digit (5) is excluded from the prime side — that is division by 5, not by the
  wheel.
* **The dichotomy is a one-way statement.** It forbids an odd capacity; it does not forbid an even prime
  (2 is one).
* **The property surface is not one scale.** $EN$ needs group and period, the mass needs only $Z$,
  the radius only $m$; there is no single number reproducing all four, and I have not found one.
