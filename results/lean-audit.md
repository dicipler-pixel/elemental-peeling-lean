# Audit: `scale-theorems.lean` against its source

**Scope.** 23 declarations in [`scale-theorems.lean`](scale-theorems.lean) against the claims of
[`theorem.md`](theorem.md) §1–4. **This is a self-audit, not an independent review** — the same process
wrote both sides. [`promotion-theorems.lean`](promotion-theorems.lean) (27 declarations) is audited in
§6 below, added later.

**Commands run** (`lean` 4, Mathlib from `/opt/mathlib`):

```
lean results/scale-theorems.lean            # 0 errors, 0 warnings, no output
grep -c sorry results/scale-theorems.lean   # 0
#print axioms <each of the 23>              # ⊆ {propext, Classical.choice, Quot.sound}
```

Axiom report, complete: `propext` and `Quot.sound` on 20; those two plus `Classical.choice` on the three
that use `Finset` sums (`widths_sum`, `rung_width`); `propext` alone on the two `norm_num` numerals
(`inventory`, `closures_next`, `seven_187`). **No `sorryAx`, no project axiom, no `native_decide`.**

---

## 1. Statement by statement

| source claim (`theorem.md`) | declaration | verdict |
|---|---|---|
| (i) twin starts are $\equiv2\pmod3$ | `prime_mod3` (from `Nat.Prime p`, `Nat.Prime (p+2)`, `5 < p`) and `class_mod3` (from the residue) | **matches, and now derived from primality** |
| (i) the three twin classes | `twin_class` (from primality) | **matches** |
| (i) $q-p\equiv0\pmod6$ | `twin_gap_mod6` | matches; hypotheses are the residue facts, not primality |
| (i) air $\equiv4\pmod6$ | `air_mod6` | matches |
| (i) five classes mod 30 | `air_five_classes` | matches |
| (i) class $\leftrightarrow$ digit | `class_digit_inj` | matches: injectivity on five elements, hence bijective |
| (i) $T=\text{air}+4$ shifts the class | `total_class` | matches for all five classes |
| (i) the carry | `carry_mod3` | matches the mod-3 fact; the "gap 2 cannot follow" is its reading |
| (i) capacity 7 | `row_capacity_seven` **and** `seven_dvd_not_prime` | **two pieces, not one** — see O2 |
| (i) run ≤ 5 | `run_bound` **and** `seven_187` | arithmetic only — see O1 |
| (ii) $\sum_{l<m}2(2l+1)=2m^2$ | `widths_sum` | matches, by induction |
| (ii) $W(q)=2\lceil q/2\rceil^2$ | `rung_width` | matches (specialisation of the above) |
| (ii) $N(7),N(8),N(9)=118,168,218$ | `inventory`, `closures_next` | matches at the three numerals — see O3 |
| (iii) capacities even | `width_even`, `shell_even`, `width_digit_even`, `shell_digit_even`, `capacity_never_odd` | matches |
| (iv) the measured laws | — | **deliberately absent**: a fit is not a theorem |

## 2. Findings that were fixed in this pass

**F1 — the primality step was missing.** The earlier file took `p ≡ 11,17,29 (mod 30)` as a *hypothesis*
and proved the residue chain from it, while the source asserts it of twin starts. A proof of
"residue ⇒ classes" does not prove "twin start ⇒ classes". Closed by `twin_class`: from `Nat.Prime p`,
`Nat.Prime (p+2)`, `5 < p`, using `Nat.dvd_prime` to kill $3\mid p$, $3\mid p+2$, $5\mid p$, $5\mid p+2$,
then `omega` for the CRT.

**F2 — the total's shift covered one class.** `total_is_air_plus_pair` proved only `a%30 = 28 → t%30 = 2`.
Replaced by `total_class`, all five.

**F3 — a docstring described the converse.** The old `twin_start_mod3` said "a twin start lies in one of
three classes" while its statement went the other way. Renamed `class_mod3` with a docstring matching the
statement.

**F4 — the shell capacity's digit was asserted but not proved.** Added `shell_digit_even`.

## 3. Open — what the Lean does **not** establish

**O1 — the run bound is not assembled.** `run_bound` gives "among seven consecutive terms of step 30 one
is divisible by 7"; `seven_187` gives that the only survivor through 7 is composite. Assembling them into
"no column contains six consecutive gaps of 2" needs a formalisation of the column and of the run — not
present.

**O2 — capacity 7 is not assembled.** `row_capacity_seven` gives the divisibility and
`seven_dvd_not_prime` gives the compositeness, but the case analysis over the eight classes of a block,
and the identification of the classes with the block's entries, is prose.

**O3 — the depth law is a numeral, not a theorem.** `$d_l=m-2l+1$` appears only as the three evaluations
118, 168, 218. A general `depths` theorem and the sum $\sum_l w_l d_l = N(m)$ are not formalised.

**O4 — the objects are integers, not segments.** Every theorem is about `ℤ` or `ℕ` with residue
hypotheses. The definitions `air = q - p - 2`, `class = air mod 30`, "segment", "rung", "block" live in
prose. That is the largest fidelity gap: the Lean proves the *arithmetic*, and the translation from the
arithmetic to the tables is unverified.

**O5 — the exceptions (partly closed).** The exchange rule $G(k)$, the peak at the half-fill, the range,
the rung gap of every promotion and the $10+9$ split are now formalised — see §6. What is *not*
formalised is the measurements themselves: the nineteen configurations are transcribed into a list, and
the Lean checks the classification of that list, not that the list is right.

## 4. Proof status, stated separately from fidelity

Compilation: clean, no warnings. `sorry`: none. Axioms: the three standard ones, nothing else. So the 23
declarations are **proved**. That says nothing about §3: a proved statement can still be the wrong
statement, and O4 is where that risk lives.

## 5. What would raise the bar

1. Define `TwinStart p := Nat.Prime p ∧ Nat.Prime (p+2) ∧ 5 < p` and restate `twin_class` over it — then
   the primality link is a definition, not a hypothesis chain.
2. Formalise a block as `Finset (ℕ × ℕ)` with the fill order, and prove capacity 7 by the case analysis
   O2 asks for.
3. Formalise the column and the run, and finish O1.
4. Leave the fits out of Lean, or put them behind an explicit `empirical` predicate — do not dress a
   measured coefficient as proved.

---

## 6. Audit of `promotion-theorems.lean`

**Commands run:**

```
lean results/promotion-theorems.lean                          # 0 errors
grep -c sorry results/promotion-theorems.lean                 # 0 (the only hits are the word in a comment)
#print axioms <each of the 27>                                # 13 axiom-free; 14 ⊆ {propext, Classical.choice, Quot.sound}
python3 scripts/check-lean-citations.py                       # every Lean name cited in results/*.md resolves
```

[`fission-theorem.lean`](fission-theorem.lean) (30 theorems, same checks, all axioms ⊆
{propext, Classical.choice, Quot.sound}) is audited separately in §7 below: its one non-arithmetic step
is the definition of `closed`, which rests on `chain-table.md` C15 (measured on 118 elements), not on a
proof. It replaces the earlier `fission-theorems.lean`, whose content is a subset; the docstrings there
that named `four_term`, `countdown_sum` and `U_pinned` now refer to `same_period`, `split_countdown` and
`pin`.

`scripts/check-lean-citations.py` exists because of a real breakage found in this pass: `theorem.md`
cited `total_is_air_plus_pair`, which no longer existed (renamed `total_class`). The script now checks
every *(Lean: \`name\`)* citation in `results/*.md` against the declarations in `results/*.lean`, and
prints the declaration counts and any `sorry` / `admit` / `axiom`.

| source claim | declaration | verdict |
|---|---|---|
| $\Phi(k)=\binom{\min(k,\text{cap}-k)}{2}$ | `Phi` | definition, matches |
| $G(k)=k$ to the half-fill, $k+1-\text{cap}$ after | `G_d`, `G_f` | matches on $k\le9$, $k\le13$ by `interval_cases` |
| the peak is at the half-filled shell | `G_d_peak` ($+4$), `G_f_peak` ($+6$) | matches |
| the range is $\text{cap}-2$ | `G_d_spread` (8), `G_f_spread` (12) | matches |
| a unit rank cannot follow that range | `rank_cannot_follow` | matches |
| no promotion crosses two rungs | `promos_gap_le_one` | matches on the transcribed nineteen |
| rung $+1$ ⟹ $s\to d$, rung $0$ ⟹ $f\to d$ | `gap_one_is_s_to_d`, `gap_zero_is_f_to_d` (general arithmetic) + `promos_gap_one_shape`, `promos_gap_zero_shape` (the list) | **two layers**: the arithmetic is general, the application is a finite check |
| ten and nine | `promos_split` | matches |
| three rational rungs reproduce the $d$ flip sets | `fit_3d`, `fit_4d`, `fit_5d` | **verified as a fit**: witnesses $A,B$ are written down and the flip set is computed |
| no linear rung fits the $f$ series | `f_straddle_forces_B` | matches, but *within the linear-rung model* — it is not a statement that no model fits |

**Fidelity, stated plainly.** Three things are prose, not Lean: (a) that the nineteen configurations are
the measured ones — `promos` is a transcription; (b) that a promotion is a *one-electron* transfer between
the subshell the rule fills and the subshell observed — the list encodes the pair of subshells, not the
count of electrons moved (Pd and Th move two, and the list has one row each); (c) that the observations
are defined as they are in the tables. So the file proves the *classification of a given list*, and the
list's provenance is measurement.

---

## 7. Audit of `fission-theorem.lean`

**Scope.** The 30 theorems of [`fission-theorem.lean`](fission-theorem.lean) against the statement in
[`fission-theorem.md`](fission-theorem.md) §1, parts (I)–(VI). Self-audit, same caveat as above.

```
lean results/fission-theorem.lean     # 0 errors, 0 warnings, no output
grep -c sorry results/fission-theorem.lean   # 0 (the word appears only in the header comment)
#print axioms <each of the 30>        # ⊆ {propext, Classical.choice, Quot.sound}
python3 scripts/fission_verify.py     # 24 checks on the measured parts, 0 mismatches
```

| source claim | declaration | verdict |
|---|---|---|
| the table: `v + h = L(m)` on all 118 cells | `cell_identity`, `counted_eq` | **matches**; the countdown identity is now checked on every cell, where `scale-theorems.lean` had it only as a ring identity |
| (I) $h_1+h_2 = C_1+C_2-Z$ | `split_countdown` | matches, from $Z_1+Z_2=Z$ alone |
| (I) two pieces in one period | `same_period` | matches; hypothesis-free identity |
| (I) exact conservation | `split_conserves` | matches |
| (I) symmetric needs even $Z$ | `symmetric_needs_even` | matches |
| (II) the pin | `pin` | matches for $91\le Z\le108$ — **and not below**: for $Z\le90$ the light piece has fallen into an earlier period, where $h\ne108-Z$. The first draft of the statement got this wrong and `decide` caught it. |
| (III) closed splits of 92, 94, 96 | `closed_split_U/_Pu/_Cm` | match, three windows, case-checked |
| (IV) the switch at 98 | `symmetric_closed` | matches |
| (V) thorium | `double_closure_only_th`, `th_closures_add`, `light_closed_five` | match |
| (VI) inventory, saturation | `inventory`, `rungs_to_eight`, `every_cell_below_118` | match |

**O6 — the definitions are the table's, not nature's.** `C`, `L`, `period`, `cnt` and `closed` encode the
Light Bridge table. That the real periodic table *is* this table is the measured content of
`light-bridge-theorem.md` (C15, 118 elements, no exceptions), not something this file proves. So the Lean
proves: *given this table*, a split has these properties — and the table's fidelity is a separate,
measured claim.

**O7 — nothing about dynamics.** Parts (I)–(VI) are statements about counts. Why a nucleus splits, how
often, and with what neutron multiplicity is outside the file and outside the table (a $Z$-indexed table
cannot see neutrons).

**Proof status, separately.** Clean compile, no warnings, no `sorry`, no custom axiom. The 30 theorems
are proved. Whether they are the *right* 30 is the question O6 bounds.

---

## 8. `master-theorem.lean` — the collected statement

42 theorems restating parts (A)–(L) of [`master-theorem.md`](master-theorem.md) in one self-contained
file: the table is defined there, so a single `lean results/master-theorem.lean` verifies the master
statement end to end. It deliberately repeats material from the specialist files; `bash
scripts/verify-all.sh` compiles all seven and checks every axiom, so a divergence between them shows up
as a failure rather than as drift. Part (K) — the force assignment — is the one part whose *content* is
identification rather than arithmetic: its Lean theorems are the arithmetic it rests on
(`trivial_zeros_even`, `critical_line_fixed`, `wheel_is_euler`, `period_is_2n2`, `capacities_are_2n2`, `coulomb_cumulant`, `oscillator_cumulant`,
`coulomb_oscillator_agree`, `oscillator_beats_coulomb`, `proton_meets_magic_only_at_two`,
`oscillator_meets_magic`, `fissility_band`, `fissility_narrow`), and the identifications
themselves are argued, not proved. Same caveat as O6: the file proves statements about *this* table, and
that the periodic table is this table is `chain-table.md` C15 — measured on 118 elements.
