# Capacities with bonds: what saturates, and how the ladders align

## 1. The bonding capacities are the table's own period lengths

| rule | number | equals |
|---|---|---|
| duet | 2 | $L(1)=2$ |
| octet | 8 | $L(2)=L(3)=8$ |
| 18-electron | 18 | $L(4)=L(5)=18$ |
| 32-electron | 32 | $L(6)=L(7)=32$ |

$$2,\ 8,\ 18,\ 32 \;=\; 2m'^2\ (m'=1,2,3,4) \;=\; L(m),$$

so the numbers chemistry saturates at are the numbers the Chain Table already computes: the period
lengths $2\lceil(m+1)/2\rceil^2$ and the block sums $\sum_{l<m'}2(2l+1)=2m'^2$. **The octet is not a
separate law; it is the length of period 2.** The 18-electron rule is the length of period 4, the
32-electron rule the length of period 6.

## 2. The countdown is the unmet capacity

With $v$ the valence count and $h=C(m)-Z$ the countdown:

$$v+h=C_{\rm block},\qquad C_{\rm block}=\begin{cases}L(m), & s\\ 8, & p\\ 18, & d\\ 32, & f\end{cases}$$

— **117 of 118**, the exception being He (its group entry is 18, its valence 2). The $s$ block's capacity
is the period's own length $L(m)$, because $s$ *opens* the period, and the $f$ block's valence is its
count beyond the closure (3 to 16), not the tabulated 3. The earlier "82 of 118" came from giving $s$ the
octet and $f$ the fixed valence 3; both faults and the exact identity underneath are worked out in
`e2-adjustment.md`.

**Bonds** $=\min(v,h)$ for the main group, and the maximum over all 118 main-group elements is
**4**. That is the real content of the octet: $\min(v,8-v)\le4$, with equality at group 14. B gives 3 of
its 5 vacancies (a vacant orbital left — the Lewis acid), C 4 of 4, N 3 of 3, O 2 of 2, F 1 of 1.

**Ligands** $=h/2$ for the $d$ block, and an odd $h$ means a radical:

| | Sc | Ti | V | Cr | Mn | Fe | Co | Ni | Cu | Zn |
|---|---|---|---|---|---|---|---|---|---|---|
| $h$ | 15 | 14 | 13 | 12 | 11 | 10 | 9 | 8 | 7 | 6 |
| $h/2$ | 7.5 | 7 | 6.5 | **6** | 5.5 | **5** | 4.5 | **4** | 3.5 | 3 |

Cr(CO)₆, Fe(CO)₅, Ni(CO)₄ are exactly $h/2$ ✔, and the half-integers are the 17-electron radicals
(V(CO)₆, Mn(CO)₅, Co(CO)₄) — the parity of $h$ is the parity of the electron count, which is the same fact
as the digit dichotomy.

## 3. Ionic counting, and why 9 was never impossible

A formal charge moves the count without moving the capacity: an anion adds electrons until the next
capacity, a cation removes them. So the admissible counts are $0..2m'^2$, not $0..8$ — and 9 is a legal
count wherever the capacity is 18 or more. In the data, a shell occupation of 9 occurs **eleven times**
(Sc $3s^23p^63d^1$, Y, La, Lu, Ac, Ce, Pa, U, Np, Gd, Cm), and Cu²⁺ is $3d^9$. The octet was never a
bound on the count; it is the bound on the *neutral main-group* count.

## 4. The alignment

| | primes | elements |
|---|---|---|
| the unit | a segment (a pair of pairs) | an electron |
| the count | $m$ segments | $Z$ electrons |
| the capacity | 7 per 30-row; widths $2(2l+1)$ | $2m'^2=2,8,18,32$ |
| what saturates | the row: one multiple of 7 | the shell: duet, octet, 18, 32 |
| mass | $m$ | $M=2.619\,Z-9.36$ |
| velocity | $2ct$ (grows with $t$) | $dM/dZ=2.619$, constant |
| the step | 6 (the classes), **offset 4** (the pair) | 6, 10, 14, 18 $=6+4k$ (the blocks) |
| acceleration | $2c=1.5006$, constant in $t$ | closures' second difference $0,10,0,14,0$ |
| energy | $E=c\,m\,t^2$ | $Q=C\,\Delta T=3R\,\Delta T$ |
| specific heat | $c=1/(2C_2)=0.75739$, air offset $-2$ | $3R=24.94$ |

**Both ladders are built from the same two numbers, 6 and 4** — and this is the correction that was
missing: the prime ladder carries the 4 as well, not only the elements.

* **primes**: the classes are $4+6k$ — a **step of 6** with **offset 4**. The offset is the pair:
  $T=\text{air}+4$, so the total's classes are $8+6k$, shifted by exactly one segment's worth of material.
  The offset 4 is two pairs ($2$ members $\times\,2$ pairs).
* **elements**: the rung widths are $2,2,8,8,18,18,32,32$, whose non-zero differences are
  $6,10,14,18=6+4k$ — a **first step of 6** and an **increment of 4** between steps. The 4 is two
  orbitals' worth of electrons: $w_{l+1}-w_l=2(2l+3)-2(2l+1)=4$.

So the same (6, 4) pair generates both ladders, one as (step, offset), the other as (step, step-of-steps).
The element side's increments $6,10,14,18$ are the block widths themselves $2(2l+1)$ for $l\ge1$ — the
ladder grows by the block it opens.

## 5. What changed from the earlier statements

* the bonding capacities are the period lengths, not a separate rule (§1);
* $\min(v,h)\le4$ replaces "8 is the cap on the count" — the octet caps *bonds*, not electrons (§2);
* 9 is admissible wherever the capacity is 18 (11 neutral cases, Cu²⁺ ionic) — §3 replaces "9 is
  impossible";
* and the element ladder's "acceleration" is stepwise with step 4, not uniform.
