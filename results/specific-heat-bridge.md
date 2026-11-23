# The heat capacity, read through the density triangle — and the labels that make it usable

Your triangle is the point: one relation, three readings, and you use whichever one has the unknown on
the left. Heat has exactly the same triangle, the density triangle supplies the fourth reading, and
[`specific-heat.lean`](specific-heat.lean) proves every form so that they can be used rather than
re-derived. Then the labels: nine of them, H1–H9, each with a symbol, a unit, a theorem and a status —
which is what was missing between the record's `C/3R` measurement and its use.

All the arithmetic below is in `results/specific-heat.lean` (19 theorems, 0 `sorry`); the element-side
numbers are `scripts/specific_heat_bridge.py`, which writes
[`tableW_specific_heat.csv`](tableW_specific_heat.csv).

## 1. The triangle, and its heat twin

$$\underbrace{D=\frac{M}{V},\quad M=D\cdot V,\quad V=\frac{M}{D}}_{\text{your three forms}}
\qquad\Longleftrightarrow\qquad
\underbrace{c=\frac{C}{M},\quad C=c\cdot M,\quad M=\frac{C}{c}}_{\text{the heat twin}}$$

Each is an `↔` in Lean (`triangle_density`, `triangle_volume`, `triangle_all`, `heat_triangle`), so the
triangle can be used as a rewrite in either direction — that is what "usable" means here.

Put the two together and the density triangle gives **the third reading of a heat capacity**:

$$C \;=\; c\,(D\cdot V) \qquad\text{and}\qquad \rho c \;=\; \frac{C}{V_m}
\qquad(\texttt{heat\_from\_density},\ \texttt{volumetric\_heat})$$

where $V_m = M/\rho$ is the molar volume. So the volumetric heat capacity is the molar one divided by the
molar volume, and — this is the part worth having — **Dulong–Petit makes it a prediction with nothing in
it but the molar volume**:

$$\rho c \;=\; \frac{3R}{V_m}\qquad(\texttt{dulong\_petit\_volumetric})$$

$$\boxed{\ \text{two Dulong–Petit solids with the same molar volume have the same volumetric heat capacity, whatever their masses}\ }$$

(`same_molar_volume_same_volumetric`). That box is the third reading's whole content, and it is the one
statement in this note that is exact and *not yet tested*, for the reason in §4.

## 2. The nine labels

| label | quantity | symbol | unit | theorem | status |
|---|---|---|---|---|---|
| **H1** | count capacity (a Light Bridge cell) | $L(m)=2n^2$, $w_l=2(2l+1)$ | slots | `Master.capacity_even`, `Heat.three_not_a_capacity` | **proved** — even, and 3 is not one |
| **H2** | molar heat capacity | $C$ | J mol⁻¹ K⁻¹ | `dulong_petit_molar` | **measured** $3R=24.943$, median $C/3R=1.038$ |
| **H3** | specific heat (per gram) | $c=C/M$ | J g⁻¹ K⁻¹ | `dulong_petit_gram` | **measured** $3R/M$, $r=0.9955$ |
| **H4** | volumetric heat capacity | $\rho c$ | J cm⁻³ K⁻¹ | `dulong_petit_volumetric` | **exact** given $V_m$; **untested** (§4) |
| **H5** | molar volume | $V_m=M/\rho$ | cm³ mol⁻¹ | `triangle_volume` | needs a density column |
| **H6** | the deficit | $1-C/3R$ | — | `dp_ratio_one` | **measured**, labels H6a–H6d below |
| **H7** | exchange rate | $\kappa=a/3R$ | K per unit $\log^2p$ | `conversion_is_forced`, `kappa_bracket` | conversion by definition, $\kappa=0.030364$ |
| **H8** | prime-side cell heat | $c=\Sigma T/\Sigma t^2$ | per $\log^2p$ | `segment_heat`, `segment_heat_ratio` | **measured**: 9 cells, 0.727–0.798 |
| **H9** | the parity split | $3\notin$ capacities | — | `capacity_even_heat_odd` | **proved** |

H6's four sub-labels, applied to the 78 elements that carry a molar heat, are the record's own list made
mechanical: **H6a quantum solid** ($C/3R<0.95$) 7 elements; **H6b classical** ($|C/3R-1|\le0.1$) 56;
**H6c soft** ($C/3R>1.15$) 10; **H6d weakly off** 5. So 72% of the table is H6b, and the exceptions are
named, not unexplained.

## 3. The table by the Light Bridge's own labels

**By block** (the table's own label, from $h$):

| block | n | median $C/3R$ | mean | range |
|---|---|---|---|---|
| s | 11 | 1.125 | 1.081 | 0.66–1.29 |
| p | 18 | 1.014 | 0.933 | **0.34–1.09** |
| d | 30 | 1.017 | **1.014** | **0.94–1.12** |
| f | 19 | 1.109 | 1.218 | 1.05–**2.51** |

The d block is the classical solid: 30 elements, every one within ±12% of $3R$, mean 1.4% high. The p
block is where the quantum solids live (C 0.34, B 0.44); the f block is where the anomalies live
(Am 2.51, Gd 1.49, Pu 1.42 — magnetic and heavy-fermion, not lattice). **By period:** medians
0.55 (m=2), 0.96 (3), 1.01 (4), 1.02 (5), 1.08 (6), 1.15 (7) — climbing towards $3R$ and then past it.

**The countdown — and the label that stops a false claim.** $\mathrm{Spearman}(C/3R,h)=+0.57$ over all
78 elements, which reads like "the heat follows the countdown". It does not:

| sample | n | Spearman$(C/3R,h)$ |
|---|---|---|
| all elements | 78 | $+0.569$ |
| within the s block | 11 | $+0.618$ |
| within the p block | 18 | $+0.024$ |
| within the d block | 30 | $-0.073$ |

Inside a block the countdown is flat. The overall correlation is the **composition** of blocks (the f
elements sit at high $h$ *and* high $C/3R$, for reasons that have nothing to do with $h$). This is the
same caution the manual already carries for electronegativity, and it is now measured for heat: $h$ is
not a heat coordinate. The one thing that does track the heat is the **radius**
($\mathrm{Spearman}=+0.757$) — bigger, softer lattice, closer to $3R$ — which is what a Debye temperature
does.

The 17 labelled exceptions, in full:

* **H6a, quantum solids:** C 0.341, B 0.444, Be 0.659, Si 0.793, S 0.912, Ge 0.931, Cr 0.936.
* **H6c, soft / anomalous:** Am 2.514, Gd 1.485, Pu 1.423, Cs 1.291, Rb 1.245, K 1.187, Sm 1.184,
  Np 1.181, Tb 1.159, H 1.156.

## 4. The third reading is one column short — and the radius column cannot stand in for it

The identity $\rho c = 3R/V_m$ is exact, and testing it needs $\rho$ for each element. The element table
does not carry a density column, and the radius column is **not** a molar volume — $V_m$ needs the packing
fraction and the coordination, which a radius does not have:

| element | listed $r$ | $(4/3)\pi r^3N_A$ | implied $\rho$ | $3R/V_m$ | the trouble |
|---|---|---|---|---|---|
| Fe | 140 pm | 6.9 cm³/mol | 8.07 g/cm³ | 3.60 J cm⁻³K⁻¹ | plausible |
| Cu | 135 pm | 6.2 | 10.24 | 4.02 | 14% high |
| **Au** | **135 pm** | **6.2** | **31.74** | **4.02** | same radius as Cu, 2.2× the density |
| Al | 125 pm | 4.9 | 5.48 | 5.06 | 2× high |
| C | 70 pm | 0.9 | 13.88 | 28.8 | diamond packs nothing like a sphere |

So the prediction is stated and left untested, with the reason: **one column** — density, 78 numbers —
would convert H4 from "exact" to "tested", one check per element and no fitting anywhere. Until then, H4
is the one label in the set that is proved and unmeasured, and the record says so instead of quoting it.

## 5. Why the exchange rate is not a free parameter

The two laws are $\langle\text{air}\rangle = t^2/(2C_2)-2$ on the prime side and $E = 3R\,\Delta T$ on the
solid side. Put them in correspondence, $a\,t^2 = b\,T$ with $a = 1/(2C_2) = 0.75739$ and $b = 3R =
24.943$:

$$T = \frac{a}{b}\,t^2 \qquad\text{is the \emph{only} solution}\qquad(\texttt{conversion\_is\_forced})$$

so $\kappa = a/b = 0.030364$ K per unit $t^2$ (`kappa_bracket` brackets it: $0.03036<\kappa<0.03037$).
Nothing was fitted: once the two coefficients are measured, the rate between them is arithmetic. That is
exactly why it is labelled **conversion by definition** and not a law — and why it moves by $0.9\%$ when
the air coefficient moves, which is the honest cost the record already records in
[`air-law-offset.md`](air-law-offset.md).

## 6. The tie-back to the Light Bridge, in four lines

1. **A cell's capacity is a count** (H1): $L(m)=2n^2$, $w_l=2(2l+1)$ — even, proved on every block.
2. **$3R$'s 3 is odd** (H9), so no cell can ever carry the Dulong–Petit integer: `three_not_a_capacity`
   says $2(2l+1)\ne3$ for every $l$. The same theorem that rules out an odd *digit* as a capacity rules
   out the heat capacity's 3. The two 3s are different objects — one counts spatial directions, the other
   would have to count slots.
3. **The table can still price a heat capacity**, through the $\kappa$ of H7 — one measured constant, and
   forced once the two coefficients are in.
4. **The prime side has a heat of its own** (H8): a window's $c=\Sigma T/\Sigma t^2$ is fixed by its air
   sum, its handoff count and its $\Sigma\log^2p$ — `segment_heat` gives $c\,\Sigma t^2 = \Sigma\text{air}
   + 4n$, the telescoping identity (R23) run once more. That is the object the nine cells of
   [`digit-scale-heat.md`](digit-scale-heat.md) tabulate, and it is why "specific heat" appears on both
   sides of this record without either side borrowing the other's units.

## 7. How to use it

```lean
import Mathlib
-- results/specific-heat.lean, namespace Heat
#check @Heat.triangle_all                    -- M = D·V ↔ (D = M/V ∧ V = M/D)
#check @Heat.heat_triangle                   -- C = c·M ↔ (c = C/M ∧ M = C/c)
#check @Heat.volumetric_heat                 -- C = c·D·V → D·c = C/V
#check @Heat.dulong_petit_volumetric         -- c = 3R/(D·V) → D·c = 3R/V
#check @Heat.same_molar_volume_same_volumetric
#check @Heat.dp_ratio_one                    -- C = 3R ↔ C/(3R) = 1
#check @Heat.three_not_a_capacity            -- 2(2l+1) ≠ 3
#check @Heat.conversion_is_forced            -- a t² = b T → T = (a/b) t²
#check @Heat.segment_heat                    -- c Σt² = Σair + 4n
```

| you have | you want | use |
|---|---|---|
| an element, its cell ($m$, $h$, block) | its heat label | H6a–H6d from `tableW_specific_heat.csv`; block from H1's `block` |
| mass and measured molar heat | specific heat per gram | H3 / `dulong_petit_gram` |
| specific heat and density | molar heat | H2 via H4: `C = c·D·V` |
| a molar volume | the volumetric heat capacity, predicted | H4 / `dulong_petit_volumetric` |
| a temperature difference in $\log^2p$ | kelvin | H7 / `conversion_is_forced`, $\kappa=0.030364$ |
| a window of the twin chain | its specific heat | H8 / `segment_heat` |
| a capacity from the table | whether it can be a heat capacity | H9 — no: it is even, 3 is odd |

## 8. What this does not say

* **It does not derive $3R$ from the table**, and it does not claim the table's capacities are heat
  capacities. H1 and H2/H3 are different objects; the only bridge is H7, and it is a ratio of measured
  coefficients, not an identity.
* **It does not identify the 3 of $3R$ with anything in the table.** The claim "the 3 in $3R$ and the 3 in
  the oscillator cumulant $n(n+1)(n+2)/3$ are the same 3 — spatial directions" is an **identification**
  (the weakest kind of claim the record keeps), and it is why equipartition is `(6/2)R` — three
  directions, kinetic plus potential. It is not a theorem about $L(m)$.
* **The block medians are composition, not law.** n = 11 to 30; nothing here says an element's heat is
  predicted by its block.
* **H4 is unmeasured.** No density column, no test. One column away.
