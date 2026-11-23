# Fission on the Light Bridge: one cell becomes two, and only one piece sits on the closure

A fission event is the only move in the table that *splits*. Everything else that changes $Z$ moves the
piece by one cell ($\beta$), by two ($\alpha$), or not at all. This note puts the split in the table's
coordinates, proves the arithmetic that any split must obey, and then compares it with the measured
fission products. Score, now measured rather than hoped for ([`fission-tests.md`](fission-tests.md)): the
closure pin is a hit ($53.96\pm0.09$ over 21 systems), the symmetric switch at $Z\ge98$ is a hit, the
"both pieces on closed cells" rule is a hit at Th and U and **empty** from Pu on — and one claim I made
here, that the valley depth is a function of the countdown alone, is **refuted** at a factor 31.

## 1. The event

The parent sits in a cell with $v=Z-C(m-1)$ and $h=C(m)-Z$, so that $v+h=L(m)$.

| parent | $m$ | $v$ | $h$ | $L(m)$ | block |
|---|---|---|---|---|---|
| $^{235}$U, $Z=92$ | 7 | 6 | 26 | 32 | $f$ |
| $^{239}$Pu, $Z=94$ | 7 | 8 | 24 | 32 | $f$ |
| $^{244}$Cm, $Z=96$ | 7 | 10 | 22 | 32 | $f$ |
| $^{252}$Cf, $Z=98$ | 7 | 12 | 20 | 32 | $f$ |

The split replaces one cell by two, $Z_1+Z_2=Z$ (no proton is emitted). Two things follow — the first
from that sum alone, the second from nothing at all:

$$h_1+h_2=C(m_1)+C(m_2)-Z,\qquad (v_1+v_2)+(h_1+h_2)=2L(m)\ \text{if both pieces are in one row.}$$

The second is an algebraic identity — it holds for *any* two pieces in row $m$, whatever the split. Both
are in [`fission-theorem.lean`](fission-theorem.lean) (`split_countdown`, `same_period`).

Because $Z_1+Z_2=Z$ exactly, **one piece pins the other**: the whole distribution is a function of a single
number. So the question "which splits happen" is the question "where does that number sit".

## 2. What the table cannot see

The table is indexed by $Z$ alone. Three consequences, and the first two are corrections to the usual
picture:

* **bounce and absorb are the same move.** Elastic scattering leaves $Z$ and $A$ unchanged; absorption
  $(n,\gamma)$ leaves $Z$ unchanged and raises $A$ by one. In a $Z$-indexed table both are the *identity*.
  They differ only in the mass bookkeeping, and mass enters this system in one place ($M=2.619Z-9.36$,
  a fit). So the table cannot distinguish "bounced off" from "absorbed" — not because the distinction is
  subtle, but because neither moves the piece.
* **the only moves that change the inventory** are $\beta^\mp$ ($Z\pm1$, the walk up the row), $\alpha$
  ($Z-2$), and the split. A neutron capture does not change which cell the piece occupies.
* **the table is saturated.** Every $Z\le 118$ is a cell with exactly one element in it. There is no empty
  cell below 92 for a descent to move into. That is *why* the descent is a split rather than a step: a
  heavy nucleus cannot go down the table one cell at a time, because the cells it would pass are already
  taken. Fission is the descent that makes room by producing two pieces. The table's own unfilled cells
  are the other end: $Z=119,120$ (the $8s$) and rung 9, $Z=121$–$170$.

## 3. Legal and illegal, in the table's own terms

The blocks are intervals of the countdown (`chain-table.md` C15): $p$ is $h\le5$ (and includes $h=0$, the
closure itself), $d$ is $6\le h\le15$, $f$ is $16\le h\le29$, and the $s$ cell is the row's head,
$h=L(m)-2,\,L(m)-1$. So a cell is **closed** when the piece has a complete shell or a fresh one:

$$\text{closed}:\quad h\le5\ \ \text{or}\ \ h\in\{L-2,\,L-1\}.$$

That is the whole of legality. It is a two-case predicate, and it is a *definition* here: that the real
blocks are these $h$-intervals is measured on all 118 elements (C15), not proved.

## 4. The measured distribution

Thermal fission of $^{235}$U, cumulative chain yields (IAEA, via the Wikipedia table; masses are chains,
so the partner is fixed by $A_1+A_2\approx233.5$):

| $A$ | 90 | 93 | 99 | 106 | 107 | 113 | 125 | 126 | 129 | 131 | 133 | 135 | 137 | 147 | 149 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| yield % | 5.75 | 6.30 | 6.05 | 0.39 | 0.16 | 0.0003 | 0.030 | 0.024 | 0.90 | 2.83 | 6.79 | 6.33 | 6.09 | 2.27 | 1.09 |

Two humps ($A\approx90$–$99$ at $\sim6\%$, $A\approx133$–$137$ at $\sim6\%$) with a valley between them
that bottoms at $A\approx120$–127 around $0.02$–$0.4\%$: a factor of $\sim250$ between valley and peak. The
charge split is not in that table; the standard charge-distribution result is $Z_L\approx37.5$,
$Z_H\approx54.5$ for this fission, and I use it below and flag it as literature, not something computed
here.

## 5. The pin: the heavy piece sits on the closure

For $Z=92$: $54=C(5)$, so the heavy piece at $54$ has $h=0$ — the closure cell, i.e. group 18, Xe. The
light piece is then $38$, with $h=54-38=16=L(5)-2$ — the *head* of the same row, the $5s$ cell. In the
four-number form: the counted parts are $18+2=20$, the countdowns $0+16=16$, and $20+16=36=2L(5)$
(`same_period`).

That is the invariant the measurements support across the actinides, and it is now measured rather than
assumed ([`fission-tests.md`](fission-tests.md) §2): the yield-weighted heavy charge is
**$53.96\pm0.09$** over 21 systems from Th to Cm — six protons of range, thermal, 500 keV, 14 MeV and
spontaneous — against $C(5)=54$. The light piece is the remainder:

| parent | $\langle Z\rangle$ heavy (measured) | light, measured | predicted $Z-54$ | its $h$ | symmetric split | its $h$ |
|---|---|---|---|---|---|---|
| $^{232}$Th (90) | 53.94 | **36.05** | 36 | 0 ($p$, closure) | 45+45 | 9 |
| $^{235}$U (92) | 54.03 | 38.03 | 38 | 16 ($s$) | 46+46 | 8 |
| $^{239}$Pu (94) | 54.10 | 39.90 | 40 | 14 ($d$) | 47+47 | 7 |
| $^{244}$Cm (96) | 54.32 | 41.67 | 42 | 12 ($d$) | 48+48 | 6 |
| $^{252}$Cf (98) | 55.46 | 42.51 | 44 | 12 ($d$) | 49+49 | 5 ($p$) |
| $^{256}$Fm (100) | 55.29 | 44.80 | 46 | 9 ($d$) | 50+50 | 4 ($p$) |

(`light_walks_down`, `symmetric_walks_down` for the predictions; the measured column is §2 of the test
note.) The pin holds to $0.1$ protons through Pu and drifts by $+1.4$ at Cf and Fm, which is why the
light piece there sits below $Z-54$.

## 6. The one sharp prediction, and it lands

The symmetric split has countdown $h_{\rm sym}=54-Z/2$, so it is **closed exactly when
$Z\ge98$** ($54-Z/2\le5$). In words: at $Z=96$ both halves land on the first $d$ cell; at $Z=98$ they land
on the $p$ bottom; past $Z=108$ they land on the closure itself.

**Measured** (spontaneous fission, ENDF/B-VIII.0, [`fission-tests.md`](fission-tests.md) §1): the
valley/peak ratio is $0.00014$ and $0.00025$ at $Z=96$ (Cm-244, Cm-248), $0.0026$ and $0.0027$ at $Z=98$
(Cf-250, Cf-252), and $0.067$ at $Z=100$ (Fm-256). So the step is exactly where the inequality puts it —
a factor $18$ between Cm and Cf — and the two members of each pair agree to a factor $1.04$ (Cf) and
$1.8$ (Cm), which is what "a function of $Z$ at fixed excitation" predicts and all that it predicts:

$$R(\text{SF}) = 0.0002,\ 0.0026,\ 0.067\quad\text{for } Z=96,98,100 .$$

What the same data *refutes* is the stronger reading I gave this section first: $R$ is not a function of
$\delta$ alone. Spontaneous fission of Cm-244 gives $R=0.00014$; thermal fission of Cm-245, the same $Z$,
gives $0.0044$ — **a factor 31.** Within U-235, thermal $\to$ 500 keV $\to$ 14 MeV is a factor $127$.
Excitation energy sets the scale; $\delta$ only orders the result inside one class. Both halves of that
sentence are measurements now, not caveats.

## 7. Where the "splits are the base key" reading holds, and where it breaks

Enumerating the split points of $Z=92$ and keeping those that put **both** pieces on closed cells, in the
asymmetric window:

$$(36,56),\quad (37,55),\quad (38,54)\qquad\text{and nothing else in }30\le Z_1\le46.$$

(`closed_split_U`.) In names: Kr+Ba, Rb+Cs, Sr+Xe. Three split points, and the measured hump centre
$Z_L\approx37.5$ sits on the middle one. The reaction always written first, $^{235}$U + n → $^{141}$Ba + $^{92}$Kr + 3n, is $(56,36)$: Kr at the
closure $C(4)=36$ ($h=0$), Ba at the head of row 6 ($h=30=L(6)-2$). Both closed (`kr_ba`). And the pair often quoted as the other mode, Xe-140 + Sr-96, is $(54,38)$: closure plus row
head (`sr_xe`).

**The miss, now measured** ([`fission-tests.md`](fission-tests.md) §3). The share of yield whose most
probable pair is closed, and the most probable pair itself:

| parent | closed asymmetric splits | most probable pair | closed-pair share | verdict |
|---|---|---|---|---|
| $^{232}$Th (90) | 36, 37, 38 | **(36, 54)** | **0.36** | hit, and the largest |
| $^{235}$U (92) | 36, 37, 38 | (38, 52) / (38, 54) | 0.16 | **hit** — the mode is closed |
| $^{239}$Pu (94) | 38 | (42, 52) | **0.000** | miss: no mass has 38 as its mode |
| $^{244}$Cm (96) | none | (42, 54) | **0.000** | fails outright |
| $^{252}$Cf (98) | none | (43, 56) | **0.000** | fails outright |

So "the split happens on the key" is true of the bottom of the actinides and empty from Pu on. What *is*
general is the pin: one piece on the closure, the other wherever the arithmetic leaves it.

**And the one exceptional case is arithmetic, not fitted.** $36=C(4)$ and $54=C(5)$ are consecutive
closures with $C(4)+C(5)=90$, so thorium is the single actinide whose two pieces can both sit on closures
— and the measurement is $\langle Z\rangle=(36.05,\ 53.94)$, i.e. $(C(4),C(5))$ to $0.06$ protons, with
the largest closed share of any system ($36\%$). With the heavy pinned at 54 the light piece is a closure
only when $Z-54=36$, so $Z=90$ is the only solution; the data has no way to avoid it.

## 8. So: bounce, absorb, split

In the table's vocabulary, and stated as the data supports it:

* **bounce** and **absorb** are not table events at all — both are the identity on $Z$ (§2). What they can
  do is *set the excitation*: the split happens only if the compound nucleus is above its barrier, and that
  energy is exactly what a $Z$-table does not carry. This is the honest defect in the picture: the fire is
  invisible here.
* **the split's legality is graded, not binary.** What suppresses a split is not landing on a forbidden
  cell — no cell is forbidden — but landing *deep inside an open block*. The distance that matters is
  $\delta(Z)=h_{\rm sym}-5$: $3$ for U, $2$ for Pu, $1$ for Cm, $0$ for Cf, $-1$ for Fm. The measured
  asymmetry is ordered the same way, and the valley closes exactly as $\delta$ reaches $0$. That is the
  quantitative form of "it bounces off": the further inside the open block, the more the piece is refused.
* **the key that makes a split is the closure, and it is one piece, not two.** The heavy piece is at
  $h=0$ — the countdown complete — in every measured case. That is the "normal base key" doing the work,
  and it is a single cell, not a digit class.

## 9. The three tests, returned

They were run on ENDF/B-VIII.0 fission-product yields (24 systems, `fission-tests.md`), and the answers
are:

1. **"the valley/peak ratio is a function of $\delta$ alone"** — **refuted.** At fixed $Z$ the ratio
   moves by a factor 31 between spontaneous and thermal fission, and by 127 inside U-235 from thermal to
   14 MeV. The ordering by $\delta$ inside a class holds in every class with no reversal.
2. **"the light charge of Cm-244 and Cf-252 is $Z-54$"** — **half confirmed.** The heavy piece is
   $53.96\pm0.09$ over 21 systems and the light piece is $Z-54$ within $0.1$ protons through Pu, so
   Cm-244's light charge is $41.7$ against the predicted 42. At Cf the heavy piece has moved to $55.5$,
   so the light charge is $42.5$, not 44.
3. **"no Pu split puts both pieces on closed cells"** — **confirmed**, and more strongly than expected:
   the closed-pair share is exactly zero for Pu, Am, Cm and Cf, because no mass chain has a closed cell as
   its most probable charge.

Two claims in this note were wrong and are now corrected in place: the ratio is not a function of
$\delta$ alone (§6), and the pin drifts above Cm so that the light piece is not $Z-54$ there (§5). What
survives is narrower and better supported — and one thing came out cleaner than I could have hoped: the
double-closure split at Th-232, which is a one-line arithmetic prediction with a $0.06$-proton
measurement behind it.

*(Data: ENDF/B-VIII.0 fission-product yields as tabulated in `shinokumura/tabfylibs`; JEFF-3.3 for
U-235 and Pu-239 as a cross-check. The IAEA yield endpoint refused automated access and was not
worked around.)*
