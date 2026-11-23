# The key correlations, settled — so they need not be rehashed

One line per correlation, the exact statement, its status, and where it lives. Written so that a question
already answered here is answered once: the subset-sequence rule is the model — it was re-derived twice
before it was written down, and it is item **C5** below.

Status words: **proved** (kernel-checked), **measured** (with an error or a count and a script),
**exact-by-definition**, **identification** (a reading, never a premise).

## A. The count layer — primes

| # | correlation | statement | status | where |
|---|---|---|---|---|
| A1 | the two ladders are one count | $P=B+K+2$; every prime $>3$ is $1$ or $5\pmod6$ | proved | `primeCount_partition`, `prime_mod_six` |
| A2 | twins sit on one ladder | twin start $>3$ is $5\pmod6$; $N\le K+1$ | proved | `twin_start_mod_six`, `twin_le_ladder` |
| A3 | the twin classes are three | twin start $>5$ is $11,17,29\pmod{30}$ | proved | `twin_start_mod_30` |
| A4 | air is a residue | air $\equiv4\pmod6$, total $\equiv2\pmod6$ | proved | `air_mod_six` |
| A5 | the minimal merge | a quadruplet starts at $p\equiv11\pmod{30}$ | proved | `quadruplet_start_mod_30` |
| A6 | count = span ÷ mean gap | $\sum\text{air}=\text{span}-2\hat N$ | proved | `air_sum_identity` |
| A7 | the span law | $p_N-p_1=(2C_2)^{-1}\sum\log^2p_i$, 0.022% at $10^9$ | proved given the measured constant | `span_from_logs`, `count_from_span` |
| A8 | twin density | $N=2C_2\mathrm{Li}_2$, 0.02% | measured | `count_formulas.py` |
| A9 | double-twin density | $D=(2C_2)^2\mathrm{Li}_3$, 1–2% | measured | `count_formulas.py` |
| A10 | merge rate | $D/\hat N=2C_2/\log p$, 0.5% per decade | measured | `merge-and-the-count.md` |
| A11 | merges cluster | segment-size ratios $0.99,1.06,1.15,1.23$ at $k=1..4$ | measured | `count-formulas.md` §4 |
| A12 | **no twin-side zero sum** | the twin indicator has no Euler product; a shuffle-controlled search found no peak | measured negative | `riemann-zeros.md` §2 |

## B. The zeros

| # | correlation | statement | status | where |
|---|---|---|---|---|
| B1 | the zeros are in the primes | 12 of 12 recovered below $10^7$; amplitudes on $2/\gamma$, corr. 0.9965 | measured | `zeros_in_the_primes.py` |
| B2 | **the base count has its own zeros** | $B-K=-\sum_\rho x^\rho/\rho$ over $L(s,\chi_{-3})$; 19 of 19 peaks, 25 of 25 zeros | proved form + measured spectrum | `base_key_zeros.py` |
| B3 | the trivial part is forced | trivial zeros even; critical line = fixed set of $s\mapsto1-s$; the wheel is the finite Euler product $30=2\cdot3\cdot5$ | proved | `trivial_zeros_even`, `critical_line_fixed`, `wheel_is_euler` |
| B4 | no derivation of a zero's height | the formula fixes amplitudes, never locations | structural | `count-formulas.md` §3 |

## C. Element types and the end digits

| # | correlation | statement | status | where |
|---|---|---|---|---|
| C1 | a digit is two classes | $1\leftrightarrow\{1,11\}$, $3\leftrightarrow\{13,23\}$, $7\leftrightarrow\{7,17\}$, $9\leftrightarrow\{19,29\}$; one per ladder | proved | `two_classes_per_digit`, `digit_splits_ladder` |
| C2 | the roles | openers $\{1,7,9\}$, closers $\{1,3,9\}$; 3 never opens, 7 never closes, each once (at $p=3$, $p=5$) | proved | `three_never_opens`, `seven_never_closes` |
| C3 | the dead class | 23 never starts a twin | proved | `no_twin_at_23` |
| C4 | the three pair types | $(1,3),(7,9),(9,1)$, digit step $+2\pmod{10}$ | proved | `pair_types` |
| **C5** | **the subset-sequence rule** | **a segment's class is $\bigl(2k+\sum\operatorname{cls}(a_i\bmod10)\bigr)\bmod30$, $\operatorname{cls}:4,0,6,2,8\mapsto4,10,16,22,28$; 0 exceptions in 234,287 airs and 218,241 segments** | **proved + measured** | `air_class_of_digit`, `total_class_from_digits`, `class_from_digits.py` |
| C6 | prime digits are weaker | each prime digit carries two classes; inside the twin starts one — `1→11, 7→17, 9→29` | proved | `twin_start_class_of_digit` |

## E. Segments: kindling, firewood, ratios

| # | correlation | statement | status | where |
|---|---|---|---|---|
| E1 | internal air is a prime gap | mean 22.45 (median 16), all $\equiv4\pmod6$, vs 309.7 external | measured | `kindling_segments.py` |
| E2 | kindling is inside, firewood outside | $S/V=0.178$ inside a segment, $0.013$ outside — factor 13.8 | measured | `kindling-segments.md` |
| E3 | long segments are more firewood-like | $S/V(k)=4k/\bigl((k-1)\bar a\bigr)$ with $\bar a$ the mean internal air: 0.356 (k=2) → 0.267 (3) → 0.237 (4) → 0.167 (7) | measured | `tableV3_kindling.csv` |
| E4 | the ratio band | $r=\text{air}/(\text{air}+4)\in[1/2,1)$: a segment is majority air | proved | `air_at_least_half`, `air_ratio_lt_one` |
| E5 | the ratio ladder | rungs $1\!:\!2, 5\!:\!7, 4\!:\!5, 11\!:\!13, 7\!:\!8$; $1\!:\!3$, $2\!:\!3$, $3\!:\!4$ excluded | proved | `ratio_ladder`, `no_one_third`, `no_two_thirds`, `no_three_quarters` |
| E6 | only one textbook ratio survives | $1\!:\!2$ at air $=4$, the quadruplet | proved | `one_half_at_four` |

## F. Elements: holes, heat, configurations

| # | correlation | statement | status | where |
|---|---|---|---|---|
| F1 | the block is the hole count | $h\le5$ p, 6–15 d, 16–29 f, $L-2,L-1$ s; 0 mismatches on 118 | proved+checked | `element_holes.py` |
| F2 | three hole counts | element $h$ 0–31 (total 1,355); inventory 2; shell pores $18+54+90=162$ | measured | `holes.md` |
| F3 | two closing ladders | shells at $2,10,28,60,110$; the table at $2,10,18,36,54,86,118$ (each $2n^2$ twice) | proved arithmetic | `holes.md` §3 |
| F4 | heat is universal per mole | median $C/3R=1.038$, 72% within ±10%, per gram $r=0.9955$ | measured | `specific_heat_bridge.py` |
| F5 | the heat labels | quantum 7, classical 56, soft 10, weak 5 | measured | `tableW_specific_heat.csv` |
| F6 | **heat does not follow the holes** | within block $\mathrm{Spearman}(C/3R,h)=+0.02$ (p), $-0.07$ (d) | measured negative | `configs-vs-data.md` |
| F7 | **electronegativity does** | within block $-0.80$ (p), $-0.67$ (d), $-0.92$ (s) | measured | `holes.md` §4 |
| F8 | promotions carry no heat signature | 3 in both sets against 3.7 expected, $p=0.89$; they do sit at the f-block edges ($p=0.005$) | measured | `configs-vs-data.md` |
| F9 | the volumetric reading | $\rho c=3R/V_m$; equal molar volume ⇒ equal volumetric heat | proved, **unmeasured** (no density column) | `dulong_petit_volumetric`, `same_molar_volume_same_volumetric` |
| F10 | the exchange | $\kappa=(1/(2C_2))/3R=0.030364$, forced by the two coefficients | proved conversion | `conversion_is_forced` |

## G. Fission

| # | correlation | statement | status | where |
|---|---|---|---|---|
| G1 | the pin | $\langle Z_H\rangle=53.956\pm0.094$ over 21 systems; light $=Z-54$ within 0.2 for Th–Pu | measured | `fission_verify.py` |
| G2 | **the heavy fragment is a closure** | $Z_H\to54=C(5)$, so $h(Z_H)=0$ — the heavy piece sits on the closed cell | proved arithmetic + measured pin | `pin` |
| G3 | **the closed-pair share is a position effect** | it falls monotonically with $\langle Z_L\rangle$: 0.357 (36.05) → 0.132 (38.46) → 0.077 (38.8) → **0.000 for $\ge39.8$**; the one exception is Fm-256, where the *heavy* reaches the s row head (Cs) and reopens it | measured | `tableR_fission_tests.csv` |
| G4 | which splits are closed | for $Z=92$ both pieces closed exactly for $Z_1\in\{36,37,38\}$; at 94 only 38; at 96 none; thorium is the only double closure ($36+54=90$) | proved | `closed_split_U`, `closed_split_Pu`, `closed_split_Cm`, `double_closure_only_th` |
| G5 | the fragment types | $d\to p$ 12/24, $s\to p$ 7, $d\to s$ 4, $p\to p$ 1; the light fragment moves $p\to s\to d$ with $Z$ | measured | `light-chart.md` §4 |
| G10 | **the digit ratio meets the fission ratio** | $R_{\text{digits}}=(3+9+1)/(1+7+9)=13/17=0.7647$; the pin turns it into $Z^\star=54(1+13/17)=95.29$; measured at $Z=95$: 0.7458, at $Z=96$: 0.7639 — the equation lands between them, 0.1% from Cm | forced (no fit) + measured | [`digit-ratio-equation.md`](digit-ratio-equation.md) |
| G11 | **the digit ratio does not track per system** | $R_{\text{digits}}$ is a constant of the alphabet: range 0.0018 across the chain where the fission ratio needs 0.125; correlation $r=-0.27$, shuffle $p=0.53$; the *level* still matches ($Z^\star=95.29$ against a measured crossing $96.8$, $1\sigma$) | measured negative + level agreement | [`per-system-test.md`](per-system-test.md) |
| G12 | **3 and 7 cannot come back; 1 and 9 can** | return $P(c=o)$: digit 3 → **0 of 1,141,216**; digit 7 → never a closer at all; digits 1 and 9 → 0.354. Proved by the role sets `returnable_digits`; the cause is 5 killing class 23 and the start being 5 for class 7 | proved + measured | [`locked-digits.md`](locked-digits.md) |
| G13 | **the heavy's digit is a closure-offset marker** | $R=(Z-Z_H)/Z_H$ with $Z_H$ read from the digit halves the pin's error: s.d. 2.70% → 1.16%, worst 6.1% → 2.1%; all 4 fourteen-MeV systems sit below 54 (Fisher $p=9.4\times10^{-5}$) | measured | [`locked-digits.md`](locked-digits.md) |
| G14 | **gap digits: ladder yes, driver no** | digit → class → $a/(a+4)$ with 0 exceptions; share-weighted mean 0.7726 inside the fission band; but the local composition's raw $r=-0.675$ with $Z_H-54$ collapses to $+0.076$ once the $Z$ trend is removed (which explains 73% of the offset) | proved + measured | [`gap-digits.md`](gap-digits.md) |
| A13 | **the scaled trio** | $\hat E=\text{gap}/t^2=1/(2C_2)=0.75739\pm0.000018$; $a=1/C_2=2\hat E=1.51478$; $\hat m=T/t^2=1/(2C_2)+2/t^2$ (mass is a count here, never a gram); homogeneous of degree 2, $E\rho=1$ | proved + measured | [`prime-scales.md`](prime-scales.md) |
| G6 | the ratio | $Z_L/Z_H\in[0.668,0.810]$, median 0.736, inside $[1/2,1)$ — consistency, not a test | measured | `tableV6_ratios.csv` |
| G7 | the mode is not the force balance | $Z^2/A$ spans 34.91–39.06 (factor 1.12) while the mode spans 481; the mode is ordered by $h_{\rm sym}=54-Z/2$ (Spearman $-0.80$ to $-0.89$) | proved band + measured ordering | `fissility_band`, `strong-force-bolstered.md` |
| G8 | the energy is not in the counts | a linear mass law prices every split at its intercept (8.72 GeV); the mass excess is needed | proved | `linear_mass_law_blind` |
| G9 | the ladder | closures $2n^2$ (Coulomb); the strong ladder $n(n+1)(n+2)/3$ agrees at 2, 8 and meets magic at 2, 8, 20 | proved arithmetic, identified physically | `coulomb_oscillator_agree` |

## H. The two outside theorems that carry weight here

| # | correlation | statement | status | where |
|---|---|---|---|---|
| H1 | Johnson's Theorem 10.2 | twin starts $>5$ are $2,5,8\pmod9$; it *is* the mod-3 fact | proved | `twin_mod9`, `mod9_is_mod3` |
| H2 | **the old layer's log-cosh prediction failed** | a log-cosh completion would need $a_2/a_1=-1/24$; measured $-4.9\times10^{-5}$ (850× smaller) | measured negative | `old-and-new.md` §3 |

## Settled — do not re-open

1. **$3/4$ as the air coefficient** — dead at $254\sigma$; the coefficient is $1/(2C_2)=0.75739$ and the
   offset is $-2$ (the half-pair). The $-4$ offset came from an arithmetic slip and is dead at $152\sigma$.
2. **"28 is a residue"** — 28 is a *total* on the base-key ladder; a total is not a residue. $118\equiv28$
   is a hit, and $118\equiv4\pmod6$ puts it in the base family.
3. **"Z is a fixed ratio"** — it is not: 1.0734 pairs per segment below $10^9$, drifting as
   $1/(1-2C_2/\log p)$. The **handoff** is the unit; the per-segment normalisation drifts 7%.
4. **Depth's correlator is 3**, because the two grooves differ by 10 and $10\equiv1\pmod3$
   (`depth_shift_mod3`). The 1/35 against $\alpha_W=1/31.7$ is a coincidence — do not promote it.
5. **"Exceptions"** are exchange promotions: 19 of them, 10 one-rung and 9 tie, arithmetic in
   `promotion-theorems.lean`. They carry no property signature (F8).
6. **Nine is not impossible** — the shell occupation 9 occurs 11 times; the octet bounds *bonds*, not
   occupancy.
7. **The subset sequence** (C5): a segment's class comes from its gap digits, $(2k+\sum\text{cls})\bmod30$;
   the prime digits are weaker (C6). Do not re-derive.
8. **The count per segment is not 1**: 1.0734, and it drifts; see 3.

## Open — the only things still missing

| # | needs | what it would settle |
|---|---|---|
| O1 | a **density column** (78 numbers) | F9, $\rho c=3R/V_m$ — currently proved and untested |
| O2 | the **co-paper's URL** | whether its other theorems are machine-checkable like `twin_mod9` |
| O3 | a twin-side spectral **control that survives** | nothing does yet, and A12 says nothing will |
