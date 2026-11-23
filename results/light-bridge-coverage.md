# Coverage: every claim of the Light Bridge paper against its theorem or its measurement

The paper is [`light-bridge-paper.md`](light-bridge-paper.md). This register says, claim by claim,
which kind of claim it is and where it is checked — the same discipline as the repository's top-level
`COVERAGE.md`, applied to this layer. The names are the `theorem` names in `results/*.lean`
(`namespace` prefix dropped); the scripts are in `scripts/`.

**Status key.** *proved* — a theorem, kernel-checked, axioms ⊆ {propext, Classical.choice,
Quot.sound}. *measured* — a number with an error bar, reproduced by a script. *conversion* — fixed
once two measured coefficients are fixed, proved as arithmetic. *identification* — a reading of one
object as another; never used as a premise. *not here* — not claimed.

## §1 The object

| Claim | Status |
|---|---|
| $C=(2,10,18,36,54,86,118)$ are the closures, $L(m)=2\lceil(m+1)/2\rceil^2$ the period lengths | proved: `closures_are_sums`, `capacities` |
| the cell identity $v+h=L(m)$ holds on all 118 cells | proved: `cell_identity` |
| every capacity is even, so no odd digit can label one | proved: `capacity_even`, `no_odd_capacity` |
| air $=q-p-2$ and total $T=\text{air}+4$ are the two gap readings | proved: `air_mod_six`, `total_mod_six` |
| a merge is a handoff with no prime between partner and next start | definition; counted in `scripts/count_formulas.py` |

## §2 What is proved

| Claim | Status |
|---|---|
| **(A)** $W(q)=L(q-1)$; $\sum_{l<m}w_l=2m^2$; $L(2),L(4),L(6)=8,18,32$; closures are partial sums | proved: `rung_is_period`, `widths_sum`, `capacities`, `closures_are_sums` |
| **(B)** $v+h=L(m)$ on all 118 cells | proved: `cell_identity` |
| **(C)** every capacity even; no odd capacity | proved: `capacity_even`, `no_odd_capacity` |
| **(D)** $h_1+h_2=C_1+C_2-Z$; same-period $(v_1+v_2)+(h_1+h_2)=2L$; $Z-Z_1=Z_2$; symmetric needs even $Z$ | proved: `split_countdown`, `same_period`, `split_conserves`, `symmetric_needs_even` |
| **(E)** the pin $C(5)=54$, $h(54)=0$, light $=Z-54$ with $h=108-Z$ | proved: `pin`, `light_closed_five` |
| **(F)** closed-cell splits $\{36,37,38\}$ at 92, $\{38\}$ at 94, none at 96 | proved: `closed_split_U`, `closed_split_Pu`, `closed_split_Cm` |
| **(G)** the symmetric split is closed iff $Z\ge98$ | proved: `symmetric_closed` |
| **(H)** thorium's double closure forces $Z=90$ | proved: `double_closure_only_th`, `th_closures_add` |
| **(I)** inventory $2\cdot7+6\cdot6+10\cdot4+14\cdot2=118$; rungs to $q=8$ give 120; every $Z\le118$ has a cell | proved: `inventory`, `rungs_to_eight`, `every_cell_below_118` |
| **(J)** a linear mass law prices every split at its intercept | proved: `linear_mass_law_blind` |
| **(K)** closure law is $2n^2$; the strong ladder is $n(n+1)(n+2)/3$; they agree at 2, 8; $Z^2/A$ is nearly constant while the mode spans 481 | proved: `period_is_2n2`, `oscillator_cumulant`, `coulomb_oscillator_agree`, `oscillator_beats_coulomb`, `fissility_band`, `fissility_narrow`; the "electromagnetic / strong" reading is an **identification** |
| **(L)** trivial zeros even; critical line is the fixed set of $s\mapsto1-s$; the wheel is the finite Euler product $30=2\cdot3\cdot5$, $\varphi(8)$ classes | proved: `trivial_zeros_even`, `critical_line_fixed`, `wheel_is_euler`, `wheel_has_eight_classes` |
| **(N)** twin starts $>5$ are $2,5,8\pmod 9$ with transitions $(2,4),(5,7),(8,1)$; equivalently $p\equiv2\pmod 3$ | proved: `twin_mod9`, `twin_transitions_mod9`, `mod9_is_mod3`; the mod-9 statement is Johnson's Theorem 10.2, and the reduction showing the 9 and the 3 are one fact is Beasley's |
| **(O)** $P=B+K+2$; twin $\Rightarrow5\pmod6$, $N\le K+1$; twin $\Rightarrow11,17,29\pmod{30}$; air/total residues; quadruplet class; $\sum\text{air}=\text{span}-2\hat N$ | proved: `primeCount_partition`, `twin_start_mod_six`, `twin_le_ladder`, `twin_start_mod_30`, `air_mod_six`, `total_mod_six`, `quadruplet_start_mod_30`, `air_sum_identity` |
| **(P)** density triangle and heat twin; $\rho c=C/V_m$; Dulong–Petit in three readings; equal molar volume ⇒ equal volumetric heat; $(6/2)R=3R$; $2(2l+1)\neq3$; $\kappa$ forced; window heat $c\,\Sigma t^2=\Sigma\text{air}+4n$ | proved: `triangle_all`, `heat_triangle`, `volumetric_heat`, `dulong_petit_gram`, `dulong_petit_molar`, `dulong_petit_volumetric`, `same_molar_volume_same_volumetric`, `equipartition_six`, `three_not_a_capacity`, `conversion_is_forced`, `segment_heat` |
| **(Q)** span $=(2C_2)^{-1}\sum\log^{2}p$; the $c\cdot m\cdot\Delta T$ form; the inversion for the count; $a=1/C_2$; second difference $a h^2$; velocity $at+ah/2$ | proved given the measured per-handoff law: `span_from_logs`, `span_eq_c_m_dT`, `count_from_span`, `acceleration_form`, `const_accel_second_difference`, `velocity_is_linear`; the measured side in `results/one-equation.md` |
| 212 theorems in ten files, no `sorry`, axioms ⊆ three | checked: `bash scripts/verify-all.sh`; inventory: `scripts/paper-inventory.py` |

## §3 What is measured

| Claim | Status |
|---|---|
| $\langle\text{gap}\rangle=t^2/(2C_2)$, $1/(2C_2)=0.757390$, flat to $0.001\%$ to $10^{12}$ | measured: `scripts/air_law.py`; the 3/4 reading is dead at $254\sigma$ |
| twin count $2C_2\int dt/\log^2t$ to $0.02\%$ | measured: `scripts/count_formulas.py` (column `HL_twin`) |
| double-twin count $(2C_2)^2\int dt/\log^3t$ to $1$–$2\%$ | measured: `scripts/count_formulas.py` (column `HL_double`) |
| twelve Riemann zeros below $10^7$, amplitudes on $2/\gamma$ | measured: `scripts/zeros_in_the_primes.py` |
| $L(s,\chi_{-3})$ zeros: 19 of 19 peaks, 25 of 25 zeros, power 0.955 vs 0.684 shuffled | measured: `scripts/base_key_zeros.py` |
| $\langle Z\rangle_H=53.956\pm0.094$; closed-pair share $0.357\to0.000$ | measured: `scripts/fission_verify.py`, `results/tableR_fission_tests.csv` |
| median $C/3R=1.038$, 72% within $\pm10\%$, per gram $r=0.9955$ | measured: `scripts/specific_heat_bridge.py`, `results/tableW_specific_heat.csv` |
| merge rate $p_{\rm merge}\langle t\rangle=1.327\pm0.016$ vs $2C_2=1.32032$ | measured: `results/merge-and-the-count.md` |
| $\kappa=0.030364$ K per unit $\log^2p$ | conversion: `conversion_is_forced`, `kappa_bracket`; value from `scripts/specific_heat_bridge.py` |
| the span law holds to 0.022% at $10^{9}$; $c=0.75755$ on 300 bins; no quartic term ($a_2/a_1=-4.9\times10^{-5}$) | measured: `scripts/one_equation_check.py`, `results/tableX_one_equation.csv` |
| the counts at $10^9$: $P=50{,}847{,}534$, $B=25{,}422{,}713$, $K=25{,}424{,}819$, $N=3{,}424{,}506$, $D=234{,}287$, air $=4$ 28,388 times | measured and cross-checked: `scripts/count_formulas.py` against a full sieve at $10^6$ and a second prime counter |

## §5 The relations register

R1–R17 are registered with their statuses in [`light-bridge-manual.md`](light-bridge-manual.md) §6;
R18–R28 in [`count-formulas.md`](count-formulas.md) §5; H1–H9 in
[`specific-heat-bridge.md`](specific-heat-bridge.md) §2. The paper's R-table is their summary; the
manual's is the working list.

## §6 Predictions

| Prediction | Status |
|---|---|
| P1 $\rho c=3R/V_m$ for a Dulong–Petit solid | proved as arithmetic; **unmeasured** — no density column |
| P2 no derivation of a zero's height from this layer | structural; measured zeros only |
| P3 no twin-side zero sum | **measured negative** (`results/riemann-zeros.md` §2), with the parity reason |
| P4 the count constants do not drift | measured on 289 random windows to $10^9$: mean $1.0036\pm0.045$, drift $\le0.12$ |
| P5 the inventory is 99 Madelung + 19 promotions | measured, `promotion-theorems.lean` for the arithmetic |
| P6 the pin drifts slowly ($53.96\to55.5$) | measured over 21 systems |
| P7 every claim carries one of the four labels | checked by `scripts/check-paper.py` for this paper's claims |

## What this register does not cover

The top-level repository's own papers (elemental peeling, loop wall, hypersurfaces) have their own
`COVERAGE.md`; this register covers only the Light Bridge layer in `results/`. The two layers share the
Lean toolchain and nothing else — no theorem of one is used as a premise of the other.
