# The fission theorem

A separate statement, for the fission channel alone, of what the Light Bridge table forces and what it
only measures. Everything in parts (I)–(VI) is proved in [`fission-theorem.lean`](fission-theorem.lean)
(30 theorems, 0 `sorry`, 0 `axiom`, every axiom report ⊆ {`propext`, `Classical.choice`, `Quot.sound`});
the measured parts (M1)–(M4) are checked against ENDF/B-VIII.0 by `scripts/fission_verify.py`
(24 checks, all passing).

## 0. The objects

$$C=(0,2,10,18,36,54,86,118),\qquad L(m)=2\Big\lceil\tfrac{m+1}{2}\Big\rceil^{2}=(2,8,8,18,18,32,32).$$

A cell is a count $Z$ with $m=m(Z)$ the least period whose closure covers it, and

$$v=Z-C(m-1)\ (\text{counted}),\qquad h=C(m)-Z\ (\text{countdown}),\qquad v+h=L(m).$$

The **blocks are intervals of the countdown**: $p$ is $h\le5$ (containing the closure $h=0$), $d$ is
$6\le h\le15$, $f$ is $16\le h\le29$, and the $s$ cell is the row's head, $h\in\{L-2,L-1\}$. A cell is
**closed** when $h\le5$ or $h\in\{L-2,L-1\}$.

A **fission event** replaces one cell by two: $Z_1+Z_2=Z$.

## 1. Statement

> **Theorem (fission on the Light Bridge).**
>
> **(I) Bookkeeping.** For every split, $h_1+h_2=C(m_1)+C(m_2)-Z$; if both pieces lie in one period $m$
> then $(v_1+v_2)+(h_1+h_2)=2L(m)$. The count is conserved exactly, $Z-Z_1=Z_2$ — no correction term,
> because two nuclei do not share a proton. A symmetric split needs an even parent.
>
> **(II) The pin.** $C(5)=54$, so a heavy piece at 54 sits at $h=0$: the closure cell, group 18. The light
> piece is then $Z-54$, and while that still lies in period 5 ($91\le Z\le108$) its countdown is
> $h=108-Z$ — one unit of countdown spent per proton of parent.
>
> **(III) Closed-cell splits.** In the asymmetric window $30\le Z_1\le46$: for $Z=92$ both pieces are
> closed exactly for $Z_1\in\{36,37,38\}$ (Kr, Rb, Sr against Ba, Cs, Xe); for $Z=94$ exactly for
> $Z_1=38$; for $Z=96$ for none.
>
> **(IV) The symmetric split.** Its cell is $Z/2$ with countdown $54-Z/2$; for even $Z$ in the actinide
> range that cell is closed exactly when $Z\ge98$.
>
> **(V) Thorium.** $C(4)+C(5)=36+54=90$. With the heavy piece on the closure, a light piece that is also
> on a closure ($h=0$) forces $Z=90$; and with the heavy on the closure the light piece is a *closed cell*
> for $Z=88,\dots,92$ and not above.
>
> **(VI) Inventory and saturation.** The 118 cells count $2\cdot7+6\cdot6+10\cdot4+14\cdot2=118$; the rungs
> to $q=8$ hold 120, and the two missing are the $8s$; every $Z\le118$ has a period, hence a cell. There
> is no free cell below the last closure for a nucleus to descend into one at a time — which is *why* the
> descent is a split rather than a step.
>
> **(M) Measured, not proved.** (M1) the yield-weighted heavy charge is $53.956\pm0.094$ over the 21
> systems with $Z\le96$; (M2) the light piece is $Z-54$ to within 0.2 protons across the thermal and
> spontaneous systems from Th to Pu; (M3) the share of yield whose most probable pair is closed falls from
> 0.36 (Th) to 0.16 (U) to 0.000 (Pu and above); (M4) the valley/peak ratio in spontaneous fission rises
> $0.0002\to0.0026\to0.067$ for $Z=96,98,100$.

## 2. What the Lean proves, part by part

| part | Lean | how |
|---|---|---|
| the table itself: $v+h=L(m)$ for all 118 cells | `cell_identity`, `counted_eq` | `interval_cases` + `decide`, 118 cases |
| (I) countdowns of a split | `split_countdown` | `omega`, from $Z_1+Z_2=Z$ alone |
| (I) two pieces in one period | `same_period` | `ring` — an identity, no hypothesis |
| (I) exact conservation | `split_conserves` | `omega` |
| (I) symmetric needs an even parent | `symmetric_needs_even` | `omega` |
| (II) the pin | `pin` | `interval_cases`, 18 parents |
| (III) uranium | `closed_split_U` | 17 cases, each `simp`/`decide` |
| (III) plutonium | `closed_split_Pu` | 18 cases |
| (III) curium | `closed_split_Cm` | 19 cases |
| (IV) the switch at 98 | `symmetric_closed` | 10 even parents |
| (V) the double closure | `double_closure_only_th`, `th_closures_add` | 13 cases; `simp` |
| (V) the five closed lights | `light_closed_five` | 9 cases |
| (VI) the inventory | `inventory`, `rungs_to_eight` | `norm_num` |
| (VI) saturation | `every_cell_below_118` | 118 cases |
| (III)/(V) the quoted pairs | `kr_ba`, `sr_xe`, `light_walks_down`, `symmetric_walks_down`, `th_double_closure` | `simp` on numerals |

The proofs are finite: every "exactly" in (III)–(V) is a case check over the window, and every identity
in (I) is linear arithmetic. Nothing is assumed about fission beyond $Z_1+Z_2=Z$.

## 3. The measured parts, with their numbers

Data: ENDF/B-VIII.0 fission-product yields, 24 systems (thermal, 500 keV, 14 MeV, spontaneous), JEFF-3.3
for U-235 and Pu-239 as a cross-check; provenance and format in [`fission-tests.md`](fission-tests.md) §0.
The derived tables are [`tableR_fission_tests.csv`](tableR_fission_tests.csv) and
[`tableS_fission_parity.csv`](tableS_fission_parity.csv).

**(M1) The pin.**

$$\langle Z\rangle_{\rm heavy}=53.956\pm0.094\ \text{(s.e., 21 systems, s.d. }0.43),\qquad C(5)=54,$$

and as a slope, $d\langle Z\rangle_H/dZ=0.08$ per proton against $0.59$ for a charge-density rule. Above
Cm the pin drifts: 55.5 at Cf and Fm.

**(M2) The light piece.**

| system | $\langle Z\rangle_{\rm light}$ | $Z-54$ | difference |
|---|---|---|---|
| Th-232 (500 keV) | 36.05 | 36 | $+0.05$ |
| U-235 (thermal) | 38.03 | 38 | $+0.03$ |
| Pu-239 (thermal) | 39.90 | 40 | $-0.10$ |
| Cm-244 (SF) | 41.67 | 42 | $-0.33$ |
| Cf-252 (SF) | 42.51 | 44 | $-1.49$ |

U-238 is the one system outside the pattern, and physically so: its fission is thresholded even at
500 keV, and the light piece sits $+0.46$ there and $+0.92$ at 14 MeV.

**(M3) Closed-cell shares.**

| | Th-232 | U-233 | U-235 | Np-237 | Pu-239 | Am-241 | Cm-244 | Cf-252 |
|---|---|---|---|---|---|---|---|---|
| share | **0.357** | 0.200 | 0.158 | 0.083 | **0.000** | **0.000** | **0.000** | **0.000** |

**(M4) The symmetric split and the valley.** Valley/peak in spontaneous fission: $0.00014$ (Cm-244),
$0.00025$ (Cm-248), $0.00257$ (Cf-250), $0.00267$ (Cf-252), $0.0673$ (Fm-256) — a factor 18 across the
$Z=98$ step. And at fixed $Z$ the excitation dominates: Cm-245 thermal / Cm-244 spontaneous $=31.4$.

**(M5) Parity, the element-side analogue of "the unit is not one".** Even/odd $Z$ yield $=1.635$ for
U-235 thermal (1.781 in JEFF-3.3), $1.096$ for Cf-252 — so "one unit per fragment" is not fixed either,
and its bias decays with $Z$.

## 4. What the theorem does not contain

* **Why it splits.** The barrier, the saddle, the scission dynamics — none of it is in a table of counts.
  The table says where pieces land; it says nothing about whether they do.
* **Neutrons.** The table is indexed by $Z$ alone, so a neutron capture is the identity on it, elastic
  scattering is the identity, and the neutron multiplicity $\bar\nu\approx2.4$ is invisible. Bounce and
  absorb cannot be told apart here — not because the distinction is fine, but because neither moves the
  piece.
* **The width.** (M1) is about a mean: individual fragments spread with s.d. $2.3$ around 54. The pin is
  a property of the distribution's centre, not of any single event.
* **Any merge correction.** Unlike the prime ladder, where a segment can carry 1–7 pairs and the count
  per segment drifts ([`merge-and-the-count.md`](merge-and-the-count.md)), $Z$ here is a proton count
  and is additive with no correction. That asymmetry is a fact about the two objects, not a defect.
* **And a second coordinate does not rescue the physics** — it buys the neutrons exactly and the
  structure not at all; see [`the-second-coordinate.md`](the-second-coordinate.md) and §9 of the Lean
  file (`capture_moves_N`, `neutron_unpinned`, `ladders_share_one`).

## 5. Verification — one command each

```sh
lean results/fission-theorem.lean                  # 30 theorems, 0 errors, 0 warnings, no sorry
python3 scripts/check-lean-citations.py            # every Lean name cited in results/*.md resolves
python3 scripts/fission_verify.py                  # rebuilds the tables, then 24 checks on (M1)–(M5)
```

The axiom report is produced by the checker (it appends `#print axioms` to a copy of the file, so the
delivered file itself stays output-free):

```
period_lengths propext · cell_identity propext · split_countdown propext Quot.sound
same_period propext Quot.sound · pin propext · closed_split_U propext Classical.choice Quot.sound
… all 30 ⊆ {propext, Classical.choice, Quot.sound}; no sorryAx, no native_decide, no project axiom.
```

Current state of `fission_verify.py`: **24 checks, 0 mismatches** — including the two that were wrong in
the earlier draft of the note and were corrected by this script: the "within 0.2 protons" claim now
excludes U-238, and the closed share for U-235 is quoted for the ENDF evaluation (0.158) with JEFF-3.3
(0.188) carried as a separate cross-check.
