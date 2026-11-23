# A new periodic table keyed on last digit — and what it actually buys

Built from the 118 elements (Bowserinator/Periodic-Table-JSON), measured against the Relational
Atlas idiom: classes, floors, capacity, and an end-digit key. Everything below is computed; the
information figures are bias-corrected by 400 permutations per modulus.

## The end-digit table

Each last digit is a diagonal of the standard table (Z, Z+10, Z+20, …):

| last digit | count | elements |
|---|---|---|
| 0 | 11 | Ne10 Ca20 Zn30 Zr40 Sn50 Nd60 Yb70 Hg80 Th90 Fm100 Ds110 |
| 1 | 12 | H1 Na11 Sc21 Ga31 Nb41 Sb51 Pm61 Lu71 Tl81 Pa91 Md101 Rg111 |
| 2 | 12 | He2 Mg12 Ti22 Ge32 Mo42 Te52 Sm62 Hf72 Pb82 U92 No102 Cn112 |
| 3 | 12 | Li3 Al13 V23 As33 Tc43 I53 Eu63 Ta73 Bi83 Np93 Lr103 Nh113 |
| 4 | 12 | Be4 Si14 Cr24 Se34 Ru44 Xe54 Gd64 W74 Po84 Pu94 Rf104 Fl114 |
| 5 | 12 | B5 P15 Mn25 Br35 Rh45 Cs55 Tb65 Re75 At85 Am95 Db105 Mc115 |
| 6 | 12 | C6 S16 Fe26 Kr36 Pd46 Ba56 Dy66 Os76 Rn86 Cm96 Sg106 Lv116 |
| 7 | 12 | N7 Cl17 Co27 Rb37 Ag47 La57 Ho67 Ir77 Fr87 Bk97 Bh107 Ts117 |
| 8 | 12 | O8 Ar18 Ni28 Sr38 Cd48 Ce58 Er68 Pt78 Ra88 Cf98 Hs108 Og118 |
| 9 | 11 | F9 K19 Cu29 Y39 In49 Pr59 Tm69 Au79 Ac89 Es99 Mt109 |

Ten diagonals, each 11–12 elements, evenly spaced by 10. It is a complete, exact repartitioning of
the 118 elements — and it is the only thing a last-digit key can be.

## What it buys: almost nothing, and one thing

Bias-corrected mutual information over a shuffled null (400 permutations), in bits:

| modulus | classes | excess on **group** (H = 3.795) | excess on **block** (H = 1.909) |
|---|---|---|---|
| 2 | 2 | **+0.608** | −0.020 |
| 8 | 8 | +0.481 | −0.086 |
| 9 | 9 | +0.275 | +0.005 |
| **10** | 10 | **+0.111** | **−0.142** |
| 18 | 18 | +0.390 | −0.001 |
| **30** | 30 | **−0.027** | **+0.014** |
| 16 | 16 | +0.467 | +0.120 |
| 32 | 32 | +0.662 | +0.298 |

Two hard readings:

1. **Mod 10 and mod 30 explain less than chance about the block.** −0.142 and +0.014 bits against a
   null of 0.188 and 0.646. A last-digit key is not merely weak on the periodic table, it is
   *anti-informative* for where an element sits by block.
2. **The one real content of any residue key is parity.** Mod 2 alone gives +0.608 of the group's
   3.795 bits — 16% of the group's entropy for one bit of key. Moving up a period flips parity
   (period lengths are even), so parity is exactly "horizontal position parity". Everything else in
   the table comes from the shell, not from the residue.

## The diagonal that *is* chemical is +9, not +10

The textbook diagonal relationships are

| pair | ΔZ | mod 9 | mod 10 |
|---|---|---|---|
| Li(3) → Mg(12) | 9 | 3 → 3 ✔ | 3 → 2 ✘ |
| Be(4) → Al(13) | 9 | 4 → 4 ✔ | 4 → 3 ✘ |
| B(5) → Si(14) | 9 | 5 → 5 ✔ | 5 → 4 ✘ |
| C(6) → P(15) | 9 | 6 → 6 ✔ | 6 → 5 ✘ |
| N(7) → S(16) | 9 | 7 → 7 ✔ | 7 → 6 ✘ |
| O(8) → Cl(17) | 9 | 8 → 8 ✔ | 8 → 7 ✘ |

One period down and one group right is $+8+1 = 9$. So the chemically meaningful diagonal class is
$\bmod 9$, and the end-digit classes cut straight across it. And the relationship dies after period
3, because from period 4 the row is 18 wide, not 8 — the +9 disappears. A modulus that only works
while the period length is 8 is not a modulus of the table; it is a modulus of two of its rows.

## Why no residue key can ever be exact here

The table's own ladder is the shell closures (the noble gases):

$$2,\ 10,\ 18,\ 36,\ 54,\ 86,\ 118 \qquad\text{steps}\qquad 8,\ 8,\ 18,\ 18,\ 32,\ 32 = 2n^2 .$$

Those steps are a *growing* sequence, so their residues are not constant in any modulus:

| steps mod | residues |
|---|---|
| 8 | 0, 0, 2, 2, 0, 0 |
| 9 | 8, 8, 0, 0, 5, 5 |
| 10 | 8, 8, 8, 8, 2, 2 |
| 30 | 8, 8, 18, 18, 2, 2 |

No modulus makes the period length constant, because the period length **is** $2n^2$. A residue key
needs a fixed modulus; the table has a growing one. The only exact key to the table is $n$ itself —
which is what the table always was.

## The synthesis: fixed capacity vs growing capacity

This is where the two models genuinely inform each other, and it is one axis:

| | her prime/twin key | the periodic table |
|---|---|---|
| generator | a fixed wheel, $30 = 2\cdot3\cdot5$ | a growing shell, $2n^2$ |
| floors / closures | 4, 10, 16, 22, 28 (mod 30) | 2, 10, 18, 36, 54, 86, 118 |
| step | 6, constant | 8, 8, 18, 18, 32, 32 — growing |
| capacity between closures | **fixed: at most 7 primes per 30** | **growing: $2n^2$ electrons in shell $n$** |
| key | exact, residue class | exact, shell index |
| residue key | 0 exceptions in 224M handoffs | measured: −0.142 bits, worse than chance |

So the transferable principle is: **a system with a fixed capacity reuses residue classes; a system
with a growing capacity must open a new shell each time.** Her key is exact on the primes because
the primes' capacity is fixed — seven to a wheel, always. The moment a system's capacity grows, the
residue key stops carrying information and the shell index takes over. That is measurable, and it is
why an end-digit periodic table cannot work while an end-digit prime key does.

And the capacity itself is the same idea in both places: "can only stack so high" is **Pauli** in the
table (two per orbital, $2n^2$ per shell) and the **7-per-30** bound in the primes (proved from mod 7,
8 never attained). In neither does the stack *tip*: the shell fills and the next one opens; the block
fills and the next 30-block begins. A capacity, not a collapse — the same verdict as the accounting
ledger and the twin-gap floor.
