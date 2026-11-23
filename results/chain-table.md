# The Chain Table — reasserted equations and the new table

**Why a new name.** "Periodic table" names the chemical object, with its periods, groups and conventions.
What follows is a different object with the same inventory: it is indexed by the *fill order* (the rung
$n+l$), sized by the *capacity* $2(2l+1)$ and $2n^2$, and it books its exclusions. Call it the
**Chain Table**. Nothing below collides with a periodic-table statement.

---

## 1. The equations, restated

| | equation | value | note |
|---|---|---|---|
| **C1** | $w_l = 2(2l+1)$ | $2,6,10,14,18$ | block width |
| **C2** | $W(q)=\displaystyle\sum_{l<\lceil q/2\rceil}2(2l+1)=2\lceil q/2\rceil^2$ | $2,2,8,8,18,18,32,32,50$ | **rung width — new closed form** |
| **C3** | $\displaystyle\sum_{l<n}2(2l+1)=2n^2$ | $2,8,18,32$ | shell capacity (A001105) |
| **C4** | fill by increasing $(n+l,\ n)$ | rung by rung, ties by $n$ | the index |
| **C5** | $(n,l)$ filled $\iff (n+l,n)\le(8,7)$ lexicographically | 118 cells | **one cutoff, no special case** |
| **C6** | $d_0=m,\ d_l=m-2l+1\ (l\ge1)$, clamped at 0; $m$ = period | $m=7$: $7,6,4,2$ | **block depth — closed form, was a list** |
| **C7** | $N(m)=\sum_l w_l d_l$ | $N(7)=118$, $N(8)=168$, $N(9)=218$ | **the inventory and its continuation** |
| **C8** | $\sum_{q\le8}W(q)=120$, so $118=120-w_0$ | $120-2$ | **the $-2$ is the $s$-width, exactly** |
| **C9** | $\Phi(k)=\binom{u}{2}$, $u=\min(k,C-k)$; $G(k)=\Phi(k+1)-\Phi(k)=k$ if $2k\le C-2$, else $k-(C-1)$ | $0,1,2,3,4,-4,-3,-2,-1,0$ | exchange step |
| **C10** | promote $ns\to(n-1)d$ iff $G(k)>A-Bk$ | $(A,B)=(6.74,0.88),(7.51,1.88),(11.52,1.77)$ | 3d, 4d, 5d |
| **C11** | ties: $4f/5d$ at $q=7$, $5f/6d$ at $q=8$ | — | same rung, decided by the levels |
| **C12** | $w_l\bmod 10=(4l+2)\bmod 10$ | $2,6,0,4,8$ for $l=0..4$ | **one block per even digit, period 5** |
| **C13** | the chain: 19 links fill to $Z=118$, 25 to $Z=170$ | see `tableM_chain_links.csv` | the fill order as a list |
| **C14** | rung vs period: $q=m$ for $s$, $q=m+1$ otherwise | — | **the chemical period, read off the rung** |
| **C15** | countdown $h=C(m)-Z$; blocks are $h$-intervals: $p$ 0–5, $d$ 6–15, $f$ 16–29, $s$ = head 2 | — | **the block widths are interval lengths** |
| **C16** | group $=18-h$ ($p,d$), $=L(m)-h$ ($s$) | 89 of 90 | the chemical group, one line |

### What is improved over the earlier statements

1. **C2 is new.** The rung width has a closed form and consecutive rungs come in equal pairs
   ($q=2m-1$ and $q=2m$ both have width $2m^2$). Previously the widths were listed, not derived.
2. **C5 replaces the special case.** Before: depth $=\#\{n:l+1\le n\le 8-l\}$, "with the $s$ column cut
   to 7 because $8s$ is not reached". Now one lexicographic inequality does the whole table, and the
   $s$-cut is its consequence ($(8,8)>(8,7)$).
3. **C8 identifies the arithmetic deficit.** $120-2$ is not a loose "two cells": it is $w_0$, the width
   of $1s$, which is exactly the subshell sitting at $(8,8)$.
4. **The period lengths are derived, not assumed.** Period $k$ fills the $s$ of shell $k$ and then rung
   $k+1$ without its own $s$; the two widths agree because an $s$ is swapped for an $s$. That is why the
   period lengths equal the rung widths $W(2),W(3),\dots$ — the OEIS entry A093907 is this identity.
5. **The exceptions are localised by rung**: $0,0,0,0,2,6,5,6$ — none before rung 5, i.e. none before
   the first $d$.
6. **C6 and C7 are now one formula each.** The depth vector at the end of period $m$ is
   $d_0=m$, $d_l=m-2l+1$ for $l\ge1$, clamped at zero. At $m=7$ that is $7,6,4,2$ and the count is
   $118$; at $m=8$ it is $8,7,5,3,1$ and the count is $168$; at $m=9$, $9,8,6,4,2$ and $218$. The
   previously stated "$7,6,4,2$" was the $m=7$ case of a general law, not a special feature of 118.

---

## 2. The Chain Table

Rows are rungs; cells are subshells in fill order; $Z$ ranges are contiguous because the fill is.

| rung $q$ | subshells | widths | $W(q)$ | **digit** $W\bmod10$ | $Z$ range | realised | exceptions |
|---|---|---|---|---|---|---|---|
| 1 | $1s$ | 2 | 2 | **2** | 1–2 | 2 | 0 |
| 2 | $2s$ | 2 | 2 | **2** | 3–4 | 2 | 0 |
| 3 | $2p,3s$ | 6, 2 | 8 | **8** | 5–12 | 8 | 0 |
| 4 | $3p,4s$ | 6, 2 | 8 | **8** | 13–20 | 8 | 0 |
| 5 | $3d,4p,5s$ | 10, 6, 2 | 18 | **8** | 21–38 | 18 | **2** — Cr, Cu |
| 6 | $4d,5p,6s$ | 10, 6, 2 | 18 | **8** | 39–56 | 18 | **6** — Nb Mo Ru Rh Pd Ag |
| 7 | $4f,5d,6p,7s$ | 14, 10, 6, 2 | 32 | **2** | 57–88 | 32 | **5** — La Ce Gd Pt Au |
| 8 | $5f,6d,7p,8s$ | 14, 10, 6, 2 | 32 | **2** | 89–120 | **30** | **6** — Ac Th Pa U Np Cm |
| 9 | $5g,6f,7d,8p,9s$ | 18, 14, 10, 6, 2 | 50 | **0** | 121–170 | 0 | 0 |
| | | | **120** | | | **118** | **19** |

The last two rows are the arithmetic's own continuation: rung 8 stops two cells short (the $8s$), and
rung 9 — 50 cells, opening with $5g$ at $Z=121$ — is entirely unfilled.

Data: [`tableK_chain_table.csv`](tableK_chain_table.csv).

---

## 3. Where these sequences sit in the OEIS

| sequence | terms | entry | what the entry calls it |
|---|---|---|---|
| shell capacities $2n^2$ | 2, 8, 18, 32, 50, 72, 98 | [A001105](https://oeis.org/A001105) | $a(n)=2n^2$ |
| rung widths $=2\lceil q/2\rceil^2$ | 2, 8, 8, 18, 18, 32, 32 | [A093907](https://oeis.org/A093907) | elements per period, Aufbau; continues 50, 50, 72, 72 |
| closures | 2, 10, 18, 36, 54, 86, 118 | [A018227](https://oeis.org/A018227) | magic numbers; continues 168, 218, 290 |
| block widths $4l+2$ | 2, 6, 10, 14, 18 | [A016825](https://oeis.org/A016825) | $a(n)=4n+2$ |
| exchange increments | 0,1,2,3,4,−4,−3,−2,−1,0 | none found | a derived table, not an OEIS object |

Agreement is on terms, not a proof: my values agree with A001105 at $n\le8$, with A093907 through
$q=8$, and with A018227 through the seventh closure. The useful part is the *continuation*: A093907 gives
50, 50, 72, 72 next and A018227 gives 168, 218, 290, which is what C2 produces for rungs 9 and 10 and
their cumulative sums — the equations and the encyclopaedia extend the same way.

---

## 4. The continuations, checked against the OEIS

C6/C7 run forward without adjustment. Period $m$, depth vector, and count:

| $m$ | $d_l$ | $N(m)=\sum w_ld_l$ | OEIS A018227 | matches |
|---|---|---|---|---|
| 7 | 7, 6, 4, 2 | $14+36+40+28=118$ | 118 | ✔ |
| 8 | 8, 7, 5, 3, 1 | $16+42+50+42+18=168$ | 168 | ✔ |
| 9 | 9, 8, 6, 4, 2 | $18+48+60+56+36=218$ | 218 | ✔ |

and the period lengths $2\lceil(m+1)/2\rceil^2$ reproduce A093907 term for term through
$m=13$ (2, 8, 8, 18, 18, 32, 32, 50, 50, 72, 72, 98, 98).

Two things this makes visible that the table at 118 hides:

* **118 is a mid-rung cut.** The depth vector $7,6,4,2$ is *not* the pure even chain: it is
  $m-2l+1$ with the $s$ one short, because $Z=118$ stops two cells into rung 8 (the $8s$). Complete the
  rung ($Z=120$) and the vector becomes the even chain $8,6,4,2 = 8-2l$, and the count is 120.
* **the rung above is not empty in principle.** Rung 9 is 50 cells ($5g$ first at $Z=121$) and completes
  at $Z=170$; the period that ends at 168 stops at $8p$, two cells short of it — the same $s$-short
  pattern one level up. Every closure is two cells short of its rung, always the $s$.

Agreement with the OEIS is agreement of *rule* (both apply the Aufbau ordering), not evidence about
real elements past 118. What it does establish is that the closed forms are the right ones: they
produce the encyclopaedia's terms without being fitted to them.

## 5. The chain, and the digits

**The chain.** Read the table as a list of links in fill order — 1s, 2s, 2p, 3s, 3p, 4s, 3d, 4p, 5s, 4d,
5p, 6s, 4f, 5d, 6p, 7s, 5f, 6d, 7p, (8s), 5g, 6f, 7d, 8p, 9s. Nineteen links fill to $Z=118$; the
twentieth is the $8s$ that is never reached; links 21–25 are rung 9. Each link carries its width, its
width's digit, and its $Z$ range in [`tableM_chain_links.csv`](tableM_chain_links.csv).

**The digits.** The width of a block has a fixed last digit, because $w_l=4l+2$:

$$w_l\bmod 10 = 2,\ 6,\ 0,\ 4,\ 8\ \ (l=0,1,2,3,4),$$

one block per even digit, recycling with period 5. So the Chain Table labels its five blocks by the five
even digits — **the same five digits that label the prime table's five classes**. In both tables the
digit *is* the class (`class-digit-table.md`); the tables share the digit set exactly, and there is no
residue argument pairing an $s$ with a particular prime class.

## 6. The chemical layer: the table's coordinates are chemistry's

The chain is not only an accounting of capacities — its two indices are the two coordinates chemistry
reads. Let $C(m)=2,10,18,36,54,86,118$ be the closures and $h=C(m)-Z$ the **countdown**.

**Rung ↔ period (C14).** For every element, the rung of its last-filled subshell is $m$ if that subshell
is $s$ and $m+1$ otherwise. So the Chain Table's index is the period, offset by one whenever the block is
not $s$.

**Blocks are intervals of $h$ (C15).** Measured over all 118, with no exceptions:

| block | $h$ | width |
|---|---|---|
| $p$ | 0–5 | 6 |
| $d$ | 6–15 | 10 |
| $f$ | 16–29 | 14 |
| $g$ | 30–49 | 18 |
| $s$ | $L(m)-2$ … $L(m)-1$ | 2 |

The widths $2(2l+1)$ are the *lengths of these intervals* — the same numbers that give the rung widths
$W(q)$, now read along the other axis.

**Group (C16).** $	ext{group}=18-h$ for $p$ and $d$, and $L(m)-h$ for $s$: 89 of the 90 main-block
elements, He being the one convention.

**And the chemistry follows $h$.** Mean Pauling electronegativity by countdown: 2.60, 2.99, 2.53, 2.30,
2.06, 1.77, 1.44, 0.96 for $h=0..7$; $	ext{Spearman}(EN,h)=-0.922$ against $-0.356$ for the period, and
the same pattern for $IE_1$ ($-0.893$ vs $-0.538$). Two-term fits:
$ENpprox1.52+0.102g-0.169m$ ($R^2=0.83$), $IE_1pprox1239+26.7g-155m$ ($R^2=0.51$).

Full treatment, the closure grid as a picture, and the 118-element data:
[`universal-scale.md`](universal-scale.md) and [`tableN_universal_scale.csv`](tableN_universal_scale.csv).

## 7. What the table says that the periodic table does not

* the **rung** is the index, so the fill order is a coordinate, not a convention;
* every row's width is $2\lceil q/2\rceil^2$ — capacity is computed, never looked up;
* the **exclusions are a column**: $120-118=2$, and it is $w_0$;
* the exceptions land in rungs 5–8 only, which is what having four blocks ($s,p,d,f$) means;
* the continuation is arithmetic — rung 9 exists and is empty;
* every block carries one even digit (C12), and the prime classes carry the same five.
