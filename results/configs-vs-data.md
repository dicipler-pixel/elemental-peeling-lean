# Configurations against data: the nineteen promotions carry no heat signature

Two independent facts about the elements sit in this record:

* **configurations** — 19 elements fill against the rung order: ten one-rung shifts (Cr, Cu, Nb, Mo, Ru,
  Rh, Pd, Ag, Pt, Au) and nine tie cases at half-fill (La, Ce, Gd, Ac, Th, Pa, U, Np, Cm). The arithmetic
  is machine-checked in [`promotion-theorems.lean`](promotion-theorems.lean) and described in
  [`fill-order-and-promotions.md`](fill-order-and-promotions.md).
* **data** — the heat labels H6a–H6d of [`specific-heat-bridge.md`](specific-heat-bridge.md) (7 quantum
  solids, 10 soft/anomalous, 56 classical, 5 weakly off) plus electronegativity and radius from
  [`tableO_element_properties.csv`](tableO_element_properties.csv).

The new perspective is the heat label. The question is whether it re-explains the configuration anomalies,
or separates itself from them. `scripts/element_configs.py`, [`tableZ_configs_vs_data.csv`](tableZ_configs_vs_data.csv).

## 1. The cross-tabulation

| heat label | promotions | other elements |
|---|---|---|
| quantum solid ($C/3R<0.95$) | 1 (Cr) | 6 |
| soft / anomalous ($C/3R>1.15$) | 2 (Gd, Np) | 8 |
| weakly off | 1 (U) | 7 |
| classical ($\lvert C/3R-1\rvert\le0.1$) | 13 | 40 |

Anomalous in both senses: **3 of 17 promotions, 14 of 61 others.** If the two facts were independent the
expected overlap would be $19\times17/78=3.7$; the observed overlap is **3**. There is no association to
report, and the permutation tests agree:

| property | promotion mean − other mean | permutation $p$ |
|---|---|---|
| $C/3R$ (the heat deficit) | $+0.008$ | **0.89** |
| electronegativity | $+0.13$ | 0.35 |
| radius | $+4.8$ pm | 0.63 |
| molar mass | $+36$ u | 0.054 |
| countdown $h$ | $+5.0$ | **0.028** |

## 2. What the one significant line means — and does not

The promotions sit at higher countdown $h$ ($+5.0$, $p=0.028$), and that is the *composition* of blocks:
promotions are d and f elements, and d/f elements live at the bottom of their blocks. Splitting by block:

| block | promotion mean $h$ − other | $p$ | n (promo/other) |
|---|---|---|---|
| d | $-1.80$ | 0.13 | 10 / 20 |
| f | $+5.21$ | **0.005** | 7 / 12 |

So the global shift is part block composition, part a **real f-block effect**: within the f block the
promotions cluster at the *start* of the series and at half-fill (La, Ce, Ac, Th, Pa at $h=28$–$29$; Gd and
Cm at $h=22$). That is the exchange term winning where the f shell is nearly empty or half full — the
classical reading, now with a coordinate and a $p$-value.

## 3. The result, stated plainly

**The configuration anomalies carry no heat signature** ($p=0.89$ on $C/3R$; 3 observed against 3.7
expected). The elements whose heat is far from $3R$ are the *light, stiff* lattices (C, B, Be, Si, S, Ge)
and the *heavy, soft* ones (Am, Pu, Gd, Np, Cs, Rb, K) — neither group is a promotion group. That is
evidence about what the heat deficit *is*: a lattice fact (Debye temperature, magnetic and heavy-fermion
excitations), not a fact about where the last electron went.

Two corollaries follow, and both are useful:

1. **The heat label is a genuinely new coordinate**, not a relabelling of the configuration layer. If it
   were, the cross-tabulation would be diagonal; it is not.
2. **The promotion arithmetic needs no property excuse.** The nineteen are what the exchange term does, and
   they show up in the count structure and in the f-block position — not in the properties. This is the
   clean version of the record's earlier decision to stop calling them exceptions.

## 4. Where the two layers do meet

Only one place, and it is the count layer, not the property layer: the promotions are *19* because that is
how many occupancies the exchange term wins (`inventory`, `promotion-theorems.lean`), and the count layer's
$118=2\cdot7+6\cdot6+10\cdot4+14\cdot2$ is the same inventory read as slots. The heat layer's contribution
to that is H9 — the parity split: $2(2l+1)\ne3$, so a cell can never carry the Dulong–Petit 3. The two
layers are adjacent, and this note is the measurement that they are not the same layer.
