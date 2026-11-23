---
title: "A closure ladder with two channels: 273 machine-checked theorems and their measured constants"
subtitle: "The Light Bridge — the table, the prime ladder, the fission channel, and the relations between them"
author: "Jeromie Beasley"
date: "Draft — 2026-11-23"
---

# Abstract

We report an object and its two channels, in a form where every statement is either **proved** by a
kernel or **measured** with an error bar, and nothing is asserted in between.

The object is a ladder of shell closures $C=(2,10,18,36,54,86,118)$ whose period lengths are
$L(m)=2\lceil (m+1)/2\rceil^{2}$ and whose rung widths are $W(q)=2\lceil q/2\rceil^{2}$. The one
identity that organises the rest is $W(q)=L(q-1)$: the rung widths and the period lengths are one
function at two arguments. Placing a count $Z\le118$ by its countdown $h=C(m)-Z$ and its counted
part $v=Z-C(m-1)$ gives a table on which the octet, the 18- and the 32-electron rules are one
function at three indices; every capacity is even; the closures are the partial sums of the $L$; and
the table is saturated below 118, so a descent through it must be a **split**, not a step.

The two channels are the prime ladder and the fission channel, and each hangs on a single number:
On the prime side it is $1/(2C_2)$; on the fission side, the closure $C(5)=54$. The mean total gap
between twin starts is $t^{2}/(2C_2)$ with
$1/(2C_2)=0.757390$, flat to $0.001\%$ across eight decades to $10^{12}$; the twin count is
$2C_2\int dt/\log^{2}t$ to $0.02\%$; and the fluctuation of the prime count itself is resolved into
**twelve Riemann zeros below $10^{7}$** (twelve of twelve, amplitudes on $2/\gamma$ with correlation
$0.9965$, a shuffled control finding 2.34 of 12). On the fission side the heavy fragment sits at
$\langle Z\rangle=53.956\pm0.094$ over 21 evaluated systems and the light fragment is $Z-54$ within
0.2 protons for Th–Pu, with the closed-pair share falling from $0.357$ (Th) to exactly $0.000$ for
Pu and above.

Four further layers make the object usable rather than merely described: a **count layer**
(the base count, the twin ladder, the twin count and the double-twin count, each with the kind of
formula it can have — a zero sum, a telescoping identity, or a singular series); a **heat layer**
(the heat capacity in the three readings of the density triangle $M=D\cdot V$, with the volumetric
reading $\rho c=3R/V_m$ exact and one data column short of being tested); a **random-test layer**
(16,052 random draws over the count relations, zero failures, no constant drifting across four
decades); an **equation layer** (the span law $p_N-p_1=(2C_2)^{-1}\sum\log^{2}p_i$, proved as a
cumulative identity given the measured per-handoff constant, shipped with the check that recomputes every
number in it); and a **verification harness** (`bash scripts/verify-all.sh`) that recompiles all
273 theorems, checks that every axiom report is within $\{\text{propext},\ \text{Classical.choice},\
\text{Quot.sound}\}$, that no `sorry` or `native_decide` occurs, that every Lean name cited in the
prose exists, and that the measured constants quoted here are the ones the data produce.

We separate, throughout, four kinds of claim — **proved**, **measured**, **conversion by
definition**, and **identification** — because the record's failure mode is not arithmetic but
grammar: a standard identity can be true and still say nothing about the world, and a measured
constant can be real and still not be a law. §7 gives the six-step protocol by which a new
scientific relation is added to the layer without breaking that separation.

# 1. The object

Let

$$C=(0,2,10,18,36,54,86,118),\qquad L(m)=2\Big\lceil\tfrac{m+1}{2}\Big\rceil^{2},\qquad
W(q)=2\Big\lceil\tfrac{q}{2}\Big\rceil^{2},\qquad w_l=2(2l+1).$$

A **cell** is a count $Z\le118$ with period $m(Z)$ the least period whose closure covers it,

$$h(Z)=C(m)-Z\ \text{(the countdown)},\qquad v(Z)=Z-C(m-1)\ \text{(the counted part)},\qquad v+h=L(m).$$

**Blocks** are intervals of the countdown: $p$ for $h\le5$ (containing the closure $h=0$), $d$ for
$6\le h\le15$, $f$ for $16\le h\le29$, $s$ for the row head $h\in\{L(m)-2,L(m)-1\}$. A cell is
**closed** when $h\le5$ or $h\in\{L(m)-2,L(m)-1\}$. A **fission event** replaces one cell by two,
$Z_1+Z_2=Z$.

On the prime side a **twin start** is a prime $p$ with $p+2$ prime; consecutive twin starts $p<q$
have **air** $=q-p-2$ and **total** $T=q+2-p=\text{air}+4$. A **handoff** is a consecutive pair; it is
**merged** when no prime lies between the departing partner $p+2$ and the arriving start $q$. A
**segment** is a maximal run of pairs joined by merged handoffs.

# 2. What is proved

Every item below is a theorem in `results/*.lean`, checked by `lean` with no `sorry` and no axiom
beyond the three standard ones; the parenthesised names are the ones to `#check`.

**(A) Counting.** $W(q)=L(q-1)$ — the bridge itself (`rung_is_period`); $\sum_{l<m}w_l=2m^{2}$
(`widths_sum`), so every block width is twice an odd number; $L(2),L(4),L(6)=8,18,32$
(`capacities`) — the octet, the 18- and the 32-electron rules are one function at three indices; the
closures are the partial sums of the $L$ (`closures_are_sums`).

**(B) Countdown.** $v+h=L(m)$ on all 118 cells (`cell_identity`).

**(C) Dichotomy.** Every capacity is even (`capacity_even`); no cell can be labelled by an odd digit
(`no_odd_capacity`). The prime alphabet $\{1,3,7,9\}$ and the capacity alphabet $\{0,2,4,6,8\}$ are
disjoint by necessity.

**(D) Split.** For every fission event $h_1+h_2=C(m_1)+C(m_2)-Z$ (`split_countdown`); if both pieces
lie in one period then $(v_1+v_2)+(h_1+h_2)=2L(m)$ (`same_period`); the count is conserved,
$Z-Z_1=Z_2$ (`split_conserves`); a symmetric split needs an even parent (`symmetric_needs_even`).

**(E) Pin.** $C(5)=54$, so a heavy piece at 54 sits at $h=0$, the closure cell (`pin`); the light
piece is $Z-54$ with countdown $108-Z$ for $91\le Z\le108$, and both pieces are closed only for
$88\le Z\le92$ (`light_closed_five`).

**(F) Closed-cell splits.** In the window $30\le Z_1\le46$: for $Z=92$ both pieces are closed exactly
for $Z_1\in\{36,37,38\}$ (`closed_split_U`); for $Z=94$ exactly for $38$ (`closed_split_Pu`); for
$Z=96$ for none (`closed_split_Cm`).

**(G) The switch.** The symmetric split is closed exactly when $Z\ge98$ (`symmetric_closed`).

**(H) Thorium.** $C(4)+C(5)=90$; with the heavy on the closure, a light piece also on a closure forces
$Z=90$ (`double_closure_only_th`).

**(I) Inventory and saturation.** $2\cdot7+6\cdot6+10\cdot4+14\cdot2=118$ (`inventory`); the rungs to
$q=8$ hold 120, so two cells are unfilled (`rungs_to_eight`); every $Z\le118$ has a cell
(`every_cell_below_118`). There is no free cell below the last closure for a nucleus to descend into
one at a time, which is why the descent is a split.

**(J) Energy is outside.** A mass law linear in $Z$ prices every split at its intercept — the linear
terms cancel (`linear_mass_law_blind`), giving 8.72 GeV for a 200 MeV process at every split point.

**(K) The ladders.** The closure law is the Coulomb degeneracy $2n^{2}$ (`period_is_2n2`); the strong
ladder is the 3D oscillator $n(n+1)(n+2)/3$ (`oscillator_cumulant`), which agrees with Coulomb at 2
and 8 and exceeds it from 18 against 20 (`coulomb_oscillator_agree`, `oscillator_beats_coulomb`), and
meets the magic numbers at 2, 8, 20 (`oscillator_meets_magic`) before spin–orbit splitting; the
fission *force balance* $Z^{2}/A$ spans only 34.91–39.06, a factor 1.12 (`fissility_band`,
`fissility_narrow`), while the *mode* — the measured part — is ordered within each excitation class by
$h_{\rm sym}=54-Z/2$ (Spearman $-0.80$ to $-0.89$), not by $Z^{2}/A$.

**(L) The zeros.** The trivial zeros are the forced lattice (`trivial_zeros_even`); the critical line
is the fixed set of $s\mapsto1-s$ (`critical_line_fixed`); the exact part of the table is the finite
Euler product $30=2\cdot3\cdot5$ with $\varphi(30)=8$ classes (`wheel_is_euler`,
`wheel_has_eight_classes`).

**(N) A theorem from the twin-prime literature, and the reduction that gives it its content.** Every
twin start above 5 is $2,5$ or $8\pmod 9$ (`twin_mod9`), with the three transitions $(2,4),(5,7),(8,1)$
(`twin_transitions_mod9`) — Theorem 10.2 of Johnson's Zenodo record (reference 7), machine-checked
here. The residues carry the statement only once the 9 and the 3 are
put together, and that is Beasley's: a prime above 3 avoids $0,3,6\pmod 9$, so the six admissible
residues pair under $+2$ as $2\to4$, $5\to7$, $8\to1$, and $p\bmod 9\in\{2,5,8\}$ **is**
$p\equiv2\pmod 3$ (`mod9_is_mod3`). The mod-9 form and the mod-3 form are one fact, and the mod-3 form
is the one the wheel already carries.

**(O) The count layer.** $P=B+K+2$ (`primeCount_partition`); every twin start above 3 is $5\pmod6$,
so $N\le K+1$ (`twin_start_mod_six`, `twin_le_ladder`); every twin start above 5 is $11,17$ or
$29\pmod{30}$ (`twin_start_mod_30`); $\text{air}\equiv4\pmod 6$ and $T\equiv2\pmod 6$
(`air_mod_six`, `total_mod_six`); a quadruplet starts at $11\pmod{30}$ (`quadruplet_start_mod_30`);
and $\sum\text{air}=\text{span}-2\hat N$ (`air_sum_identity`), the identity that makes a count a span
over a mean gap.

**(R) The end digits.** Each digit is the mod-10 shadow of two classes mod 30, one per ladder
(`two_classes_per_digit`, `digit_splits_ladder`); twin starts are the three classes 11, 17, 29, so the
openers are 1, 7, 9 (`twin_start_digit`) and the closers 1, 3, 9 (`closer_digit`); digit 3 never opens
and digit 7 never closes, each happening once at $p=3$ and $p=5$ (`three_never_opens`,
`seven_never_closes`, `the_two_exceptions`); the twin class 23 is dead (`no_twin_at_23`); and the pair
types are $(1,3),(7,9),(9,1)$ with digit step $+2$ (`pair_types`, `pair_digit_step`).

**(Q) The equation.** With the per-handoff law taken as a hypothesis, the whole chain's span is
$p_N-p_1=(2C_2)^{-1}\sum\log^{2}p_i$ (`Law.span_from_logs`); its $c\cdot m\cdot\Delta T$ form
(`Law.span_eq_c_m_dT`), its inversion for the count (`Law.count_from_span`), the per-handoff acceleration
$a=1/C_2$ (`Law.acceleration_form`) and its exact discrete content — second difference $a h^{2}$, velocity
$a t+a h/2$ (`Law.const_accel_second_difference`, `Law.velocity_is_linear`) — follow. Measured: the
cumulative form is $0.022\%$ low at $10^{9}$; fitted through the origin on 300 equal-count bins the rate is
$c=0.75755$, i.e. $1/(2C_2)$ to $0.02\%$; and a quartic term is undetectable ($a_2/a_1=-4.9\times10^{-5}$,
850 times below what a log-cosh completion would need — [`old-and-new.md`](old-and-new.md) §3).
The same layer carries the **ratio** a segment can hold: $r=\text{air}/(\text{air}+4)\in[1/2,1)$
(`air_at_least_half`, `air_ratio_lt_one`), five rungs on the classes (`ratio_ladder`), and the
exclusions `1:3`, `2:3`, `3:4` (`no_one_third`, `no_two_thirds`, `no_three_quarters`) — of the textbook
stoichiometries only `1:2` is on the ladder (`one_half_at_four`).

**(P) The heat layer.** The density triangle in all three readings (`triangle_all`) and its heat twin
(`heat_triangle`); $\rho c=C/V_m$ (`volumetric_heat`); Dulong–Petit in the per-gram, per-mole and
per-volume readings (`dulong_petit_gram`, `dulong_petit_molar`, `dulong_petit_volumetric`), with the
corollary that equal molar volume means equal volumetric heat capacity
(`same_molar_volume_same_volumetric`); equipartition $(6/2)R=3R$ (`equipartition_six`); the parity
split $2(2l+1)\ne3$, so the Dulong–Petit 3 can never label a cell (`three_not_a_capacity`); the
exchange rate is forced by the two laws (`conversion_is_forced`); and a prime window's heat is
$c\,\Sigma t^{2}=\Sigma\text{air}+4n$ (`segment_heat`).

The full inventory — 205 theorems, file by file, with each statement's lead sentence — is generated
by `scripts/paper-inventory.py` into `results/light-bridge-inventory.md`, so it cannot drift from the
files it describes.

# 3. What is measured

The constants below are not fitted inside the theorem layer; each is a measurement with an error,
reproduced by the script named, and quoted in the paper at that precision.

| quantity | value | accuracy | script |
|---|---|---|---|
| $\langle\text{gap}\rangle=t^{2}/(2C_2)$, $1/(2C_2)$ | $0.757390$ | $0.001\%$ to $10^{12}$ | `air_law.py` |
| twin count $2C_2\int dt/\log^{2}t$ | — | $0.02\%$ ($10^{7}$–$10^{9}$) | `count_formulas.py` |
| double-twin count $(2C_2)^{2}\int dt/\log^{3}t$ | — | $1$–$2\%$ | `count_formulas.py` |
| Riemann zeros below $10^{7}$ | 12 of 12 | offsets $\le0.35$; amplitude corr. $0.9965$ | `zeros_in_the_primes.py` |
| zeros of $L(s,\chi_{-3})$ from the two ladders | 19 of 19 peaks, 25 of 25 zeros | $2/\gamma$ to $0.8\%$; power $0.955$ vs $0.684$ shuffled | `base_key_zeros.py` |
| heavy-fragment charge pin | $53.956\pm0.094$ | 21 systems, s.d. $0.43$ | `fission_verify.py` |
| closed-pair share (Th → Cf) | $0.357\to0.000$ | per system | `fission_verify.py` |
| molar heat capacity | median $C/3R=1.038$ | 72% within $\pm10\%$; per gram $r=0.9955$ | `specific_heat_bridge.py` |
| merge rate | $p_{\rm merge}\langle t\rangle=1.327\pm0.016$ | against $2C_2=1.32032$ | `merge-and-the-count.md` |
| exchange rate | $\kappa=0.030364$ K per unit $\log^{2}p$ | bracket $\pm0.00001$ | `specific_heat_bridge.py` |

Every rate in this table was re-estimated from **random and regular cuts** of the chain
([`reliability.md`](reliability.md)): no cut is more than $1.5\sigma$ from the law, the per-window
$z$-scores are calibrated (s.d. $0.88$, $97.7\%$ inside two sigma), a permutation of the gaps is $3.5\times$
worse, and the two bookkeeping slips (an off-by-one in the count, a span that includes the last pair) change
the rate by $10^{-7}$ and $10^{-9}$. And the configuration anomalies were compared with the property
anomalies ([`configs-vs-data.md`](configs-vs-data.md)): the nineteen promotions carry **no** heat signature
($p=0.89$ on $C/3R$; 3 observed against 3.7 expected).

Counts at $10^{9}$, exact and independently checked (`pi(10^9)=50847534` against a second prime
counter): $B=25{,}422{,}713$ primes $\equiv1\pmod6$; $K=25{,}424{,}819$ primes $\equiv5\pmod6$;
$N=3{,}424{,}506$ twin starts; $D=234{,}287$ merged handoffs; air $=4$ exactly $28{,}388$ times.

# 4. The four kinds of claim

The register below is the discipline the rest of the paper depends on. Every sentence in the record
carries exactly one of these labels.

| kind | what it is | example | how it is checked |
|---|---|---|---|
| **proved** | a theorem about a defined object | $W(q)=L(q-1)$; $v+h=L(m)$; $\sum\text{air}=\text{span}-2\hat N$ | kernel, axiom report, no `sorry` |
| **measured** | a number with an error and a script | $1/(2C_2)=0.757390$; $\langle Z\rangle_H=53.956\pm0.094$; $N/\mathrm{Li}_2=1.000$ | the script, rerun by `verify-all.sh` |
| **conversion by definition** | fixed once two measured coefficients are fixed | $\kappa=(1/(2C_2))/3R$ | `conversion_is_forced` |
| **identification** | the weakest: a reading of one object as another | "the closure law is Coulomb"; "the 1/35 echo is the weak coupling" | stated, never used as a premise |

Two consequences are worth stating because they are the paper's main methodological claim.
*Proved does not mean physical*: the identities hold for the defined table, and whether the real
periodic table *is* that table is the measured content of a separate layer (118 elements, no
exceptions). *Measured does not mean law*: the air law is a law because it is flat across eight
decades and its coefficient is the one the twin constant predicts, not because one decade fits.

# 5. The relations register

Thirty-three relations, each with its status and its home. This is the table to extend; the manual
(`results/light-bridge-manual.md`) gives the worked recipe for using each one.

| # | relation | status |
|---|---|---|
| R1–R5 | $v+h=L(m)$; $W(q)=L(q-1)$; $\sum w_l=2m^{2}$; $L=8,18,32$; closures are partial sums | proved |
| R6–R8 | air $\equiv4\pmod6$; class ↔ digit; $V(T)=V(\text{air})+3$ | proved |
| R9–R10 | $\langle\text{gap}\rangle=t^{2}/(2C_2)$; $N=2C_2\int dt/\log^{2}t$ | measured |
| R11–R15 | split bookkeeping; the pin; closed pairs; the switch; $\nu=A-A_1-A_2$ | proved / measured |
| R16–R17 | $c=3R/M$; $\kappa=c/3R$ | measured / conversion |
| R18–R23 | $P=B+K+2$; twin $\Rightarrow5\pmod6$; $\Rightarrow11,17,29\pmod{30}$; air/total residues; quadruplet class; $\sum\text{air}=\text{span}-2\hat N$ | proved |
| R24 | $B-K=-\sum_\rho x^{\rho}/\rho$ over $L(s,\chi_{-3})$ | proved form, measured spectrum |
| R25–R28 | $N=2C_2\mathrm{Li}_2$; $D=(2C_2)^{2}\mathrm{Li}_3$; $D/\hat N=2C_2/\log x$; segments $=\hat N-D+1$ | measured |
| R37 | the whole register, with its negative results and the settled list, is [`key-correlations.md`](key-correlations.md) | — (index) |
| R36 | a segment's ratio $\text{air}/(\text{air}+4)\in[1/2,1)$; rungs 1:2, 5:7, 4:5, 11:13, 7:8; 1:3, 2:3, 3:4 excluded | proved ([`light-chart.md`](light-chart.md)) |
| R35 | each digit carries one base and one twin class; openers 1, 7, 9; closers 1, 3, 9; class 23 dead | proved ([`digit-table.md`](digit-table.md)) |
| R34 | $p_N-p_1=(2C_2)^{-1}\sum\log^{2}p_i$: span from the list, count from a span, mean gap from both | proved given the measured constant; 0.022% at $10^{9}$ |
| R29–R33 | $M=D\cdot V$ and $C=c\,M$; $\rho c=3R/V_m$; $C=3R\Leftrightarrow C/3R=1$; $3\notin$ capacities; $\kappa$ forced | proved / unmeasured / proved |

# 6. Predictions, and how each would be falsified

A relation layer is usable only if it can be wrong. These are the places it can be.

**P1. Volumetric heat capacity.** $\rho c=3R/V_m$ for any Dulong–Petit solid. *Falsified by:* two
solids with equal molar volume and volumetric heat capacities differing by more than a few percent.
*Status:* exact, untested — it needs a density column the element table does not carry, and the
radius column cannot stand in (Cu and Au are both listed at 135 pm, so they would get the same
prediction, while their densities differ by a factor 2.2).

**P2. The zeros' positions are not predicted.** The explicit formula fixes amplitudes and
frequencies, never locations. *Falsified by:* any derivation of a zero's height from this layer.
*Status:* structural; the record measures the first twelve and claims nothing more.

**P3. The twin count has no zero sum.** *Falsified by:* a twin-side spectral peak that survives a
control randomising the twin subset inside the same primality. The record looked and found none; the
prediction is that none will be found, for the parity reason in §8.

**P4. The count constants do not drift.** $N/(2C_2\mathrm{Li}_2)=1$ within $0.5\%$ on windows
and $2C_2/\log x$ for the merge rate. *Falsified by:* a window at $10^{10}$–$10^{12}$ where the
ratio leaves that band. *Status:* measured to $10^{9}$ here, to $10^{12}$ for the air law.

**P5. The inventory is Madelung plus nineteen promotions.** *Falsified by:* a twentieth promotion,
or a cell that the fill order cannot reach. *Status:* measured (99 + 19 = 118), proved for the
counts.

**P6. The pin drifts slowly.** $\langle Z\rangle_H=53.956$ at Th–Cm, drifting to $\sim55.5$ at Cf/Fm.
*Falsified by:* a system below $Z=96$ with a heavy peak outside $54\pm1$. *Status:* measured over 21
systems.

**P7. The four kinds stay separate.** *Falsified by:* any claim in the layer that is neither proved,
nor measured with an error, nor a stated conversion, nor a flagged identification. This is a
prediction about the record's own grammar, and the checker (`scripts/check-paper.py`) is what enforces
it for the claims of this paper.

# 7. How to add a relation

The point of the layer is that the next relation can be added without breaking it. Six steps, in
order; the first two decide whether the rest is possible at all.

1. **Define the object in Lean first.** A definition (`def`) that computes, so that `decide` and the
   random tests can run against it. If it cannot be defined, the relation cannot be proved, only
   measured — say so before writing anything.
2. **Decide which kind of claim it is.** Proved (state it and prove it), measured (find the estimator,
   the error bar, and the control), conversion (exhibit the two coefficients and prove the rate is
   theirs — `conversion_is_forced` is the template), or identification (write it as one, and never use
   it as a hypothesis).
3. **Write the theorem with the smallest true hypotheses**, and let the hypothesis be *named*: the two
   exceptions the random tests found in the count layer — the handoff $(3,5)\to(5,7)$ with air $0$,
   the quadruplet $(5,7,11,13)$ at $p=5$ — are exactly the hypotheses `air_mod_six` and
   `quadruplet_start_mod_30` already declare. A theorem whose hypothesis is not the exception you can
   name is not yet finished.
4. **Measure it on real data, with a control.** Every measured claim in this layer has a null
   (shuffle, alternate grouping, or a second independent counter) and the null is quoted beside the
   signal.
5. **Ask it on random inputs.** `scripts/random_count_relations.py` and `scripts/random_laws.py` are
   the templates: exact relations must have zero failures, measured laws must not drift, and the Lean
   definitions must agree with the script on random bounds.
6. **Register it and wire it.** Add the row to the manual's R-table and to
   `results/light-bridge-coverage.md` with its status and its Lean name or script; run
   `bash scripts/verify-all.sh`; the check fails if a cited name does not exist, if a quantified claim
   has drifted from the data, or if a new file has a `sorry`.

# 8. Limitations

- **The table is a defined object.** Parts (A)–(K) and (O)–(P) are theorems about it. That the real
  periodic table *is* this table is a measurement (118 elements, 99 Madelung + 19 promotions), not a
  theorem, and the theorem says how cells sit, not how many there are.
- **The ladders' force assignments are identifications.** The Coulomb and oscillator correspondences
  are exact *arithmetic* comparisons between two integer sequences; calling one electromagnetic and
  the other strong is a reading, flagged as such.
- **The twin count is a Hardy–Littlewood object.** It has no Euler product and therefore no zero sum;
  its law is measured, and the parity obstruction is why no such sum will be found.
- **Everything nuclear on the energy side is outside.** A count table cannot price a split by more
  than its intercept; the mass excess is a measured table of small differences, not a count.
- **The heat layer's third reading is unmeasured** for want of a density column, and the block
  medians are composition effects at $n=11$–$30$, not per-element laws.

# 9. Reproducibility

```
bash scripts/verify-all.sh      # everything below, in one command
lean results/master-theorem.lean            # 45 theorems, no output
python3 scripts/count_formulas.py 1e9       # the four counts, 4.7 s
python3 scripts/base_key_zeros.py 1e7 1e3 4000   # the L(s,chi_-3) zeros, 16 s
python3 scripts/specific_heat_bridge.py     # the triangle and the heat labels
python3 scripts/paper-inventory.py          # this paper's appendix
python3 scripts/check-paper.py              # the claims of this paper against the files
```

`verify-all.sh` recompiles nine Lean files (205 theorems), prints each axiom report, checks every Lean
name cited in `results/*.md` resolves, runs the ten property groups on random inputs, the Lean↔Python
cross-check, the four count checks, the $L$-function zero check, the random relation tests (16,052
draws), and the 24 fission-data checks; it prints `ALL CHECKS PASSED` only if every one of those
passes.

# Appendix A. The proved layer

| file | theorems | subject |
|---|---|---|
| `master-theorem.lean` | 45 | the master theorem, parts A–N, self-contained |
| `light-bridge-theorems.lean` | 21 | counting, the countdown, the blocks, the closures |
| `scale-theorems.lean` | 23 | the 1·3·7·9 scale, classes, the value ladder |
| `promotion-theorems.lean` | 27 | the nineteen exchange promotions |
| `merge-theorems.lean` | 12 | merged segments: total, triple, quadruplet, sextuplet, depth |
| `generative-key.lean` | 12 | what the digits generate |
| `fission-theorem.lean` | 30 | the fission channel: split, pin, closed pairs |
| `count-formulas.lean` | 16 | the four prime counts, R18–R28 |
| `specific-heat.lean` | 19 | the heat capacity, H1–H9 |
| `one-equation.lean` | 14 | the span law, its three readings, and the ratio ladder |
| `digit-roles.lean` | 20 | the four end digits: classes, roles, the dead class 23, class from digits |
| **total** | **273** | |

The statement-level inventory is `results/light-bridge-inventory.md`, generated.

# References

1. G. H. Hardy and J. E. Littlewood, *Partitio numerorum III: on the expression of a number as a sum
   of primes*, Acta Math. 44 (1923) — the singular series for prime tuples.
2. H. von Mangoldt (1895); H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer — the
   explicit formula and its truncation.
3. A. Selberg, *The general sieve-method and its place in prime number theory*, Proc. ICM (1950) — the
   parity obstruction.
4. P. L. Chebyshev (1853); M. Rubinstein and P. Sarnak, *Chebyshev's bias*, Experiment. Math. 3 (1994)
   — the ladder imbalance $B-K$.
5. R. J. Lemke Oliver and K. Soundararajan, *Unexpected biases in the distribution of consecutive
   primes*, Proc. Natl. Acad. Sci. 113 (2016) — the end-digit diagonal.
6. P. L. Dulong and A. T. Petit (1819); A. Einstein (1907); P. Debye (1912) — $3R$ and its quantum
   deficit.
7. E. Johnson, *EJ's Alternate Base Prime Number Pattern and the Twin Prime Counterflow Model*,
   Zenodo 23484151 (2026), DOI 10.5281/zenodo.23484151 — Theorem 10.2, cited as a source: the
   statement is machine-checked here as `twin_mod9`, and the mod-3 reduction that gives it its
   content is `mod9_is_mod3`.
8. Lean 4 and Mathlib — the proof assistant and library used throughout.
