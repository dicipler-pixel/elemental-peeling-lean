# Revisiting the old theorems: what actually correlates, and one prediction they made that failed

The repository holds two layers that were written at different times and for different purposes: the
**old layer** at the top level (elemental foundations, force recovery, boundary ledger, Pauli memory,
hypersurfaces, the loop wall — 1,200-plus theorems about *declared finite algebra*), and the **Light
Bridge layer** in `results/` (the closure ladder, the prime ladder, the fission channel — 212 theorems
now). The question here is how they correlate.

The first answer is the one that has to be said first: **not by dependency**. The Light Bridge files
import Mathlib and nothing else; no theorem of the old layer is a premise of any theorem of the new one,
and no constant of the old layer is used in the new one's measurements. So every correlation below is a
correlation of **form** or of **method** — and one of them is a correlation of **content**, because the old
layer's exact statement makes a prediction for the new layer's law, and that prediction can be and was
tested. It failed. §3 is the part worth the trouble.

## 1. Same form, different object

| old theorem | Light Bridge counterpart | the correspondence |
|---|---|---|
| `ScalarLedger.S_eq_log_cosh_half_t` — the scalar ledger is exactly $S=\log\cosh(\tfrac12 t)$ | $\langle\text{gap}\rangle=t^{2}/(2C_2)$ | **the same squared-log shape**: $\log\cosh(t/2)=\tfrac18t^{2}-\tfrac{1}{192}t^{4}+\dots$ is the exact form of a parabolic $t^{2}$ law. Tested in §3. |
| `LoopWall.Hall` — the power of the declared Hall model is $\sigma(x^{2}+y^{2})$, diagonalized exactly | the air law is quadratic in $t$ | same quadratic form, different variables; the Hall layer's exact negative witness ($2\sigma<c$) has the same role as the record's "the linear mass law is 44× too big" |
| `LoopWall.SpacingLaw.continuous_additive_eq_mul`, `multiplicative_laws_proportional_of_nondegenerate` | the record's *measured* $t^{2}$ exponent | a **status** correspondence, and a sharp one: the old layer proves that a law linear in $\log$ is *forced* by multiplicativity. A law *quadratic* in $\log$ is not forced by anything in that file — which is precisely why the new exponent is empirical. |
| `PauliMemory.coincident_pair_density_zero` + `noncoincident_pair_witness` — coincidence forbidden in the same-spin sector, allowed at distinct samples | `capacity_even`, `no_odd_capacity`, `three_not_a_capacity` | **the same move**: an antisymmetry or a parity kills a whole class exactly, and kills it *outside* the class's complement. Both are exclusions by structure, not by measurement. |
| `PauliMemory`'s "one retained coordinate drives two readouts" | the countdown $h$ drives both block and group | **one coordinate, two readouts** — the Light Bridge's most-used structural fact is the old layer's most-used structural fact, on different objects. |

## 2. Same method

| old practice | Light Bridge practice |
|---|---|
| `LoopWall.Archive.ordinary_count` — the kernel checks "exactly 8 of 3,570 steps outside the wall" from a CSV's exact decimals, and the prose says this is *arithmetic, not measurement* | the count layer's exact integers ($P=50{,}847{,}534$, $D=234{,}287$, air $=4$ exactly 28,388 times), checked against a second independent prime counter |
| `FalseControls/` — nine files stating plausible falsehoods that the checker rejects | every measured claim in the new layer carries a null: the shuffle for the zeros, the brute-force sieve for the counts, the alternate grouping for the depth |
| `LoopWall.Schrodinger.round_fisher_at_zero_ne_one` — the refutation kept beside the corrected `round_fisher` | the $3/4$ air coefficient, dead at $254\sigma$, kept beside the corrected $0.75739$ |
| `ElementalForceRecovery.three_force_recovery`, `four_force_recovery_with_offset` — $n$ readings determine $n$ parameters, and an unknown **offset** costs one more reading | the pin: one known closure (54) plus one measured count gives the partner (`Law.partner_from_pin`); and the missing number on the nuclear side is an **offset** — the mass excess — which is exactly the object the old layer proves how to remove, and how much it costs to remove |

## 3. The one correlation with content, and the test it produced

`ScalarLedger.S_eq_log_cosh_half_t` says the old layer's ledger is $\log\cosh(t/2)$, whose expansion is

$$\log\cosh\frac{t}{2}=\frac{t^{2}}{8}-\frac{t^{4}}{192}+\cdots=\frac{t^{2}}{8}\Big(1-\frac{t^{2}}{24}+\cdots\Big).$$

If the Light Bridge's gap law were "the same object at another scale", the quartic term would carry the
*same relative coefficient*, $a_2/a_1=-1/24=-4.2\times10^{-2}$. That is a one-line prediction, and the
chain to $10^{9}$ answers it: fitting the bin means of $\text{gap}$ against $t^{2}$ and $t^{4}$ over 300
equal-count bins gives

$$\frac{a_2}{a_1}=-4.9\times10^{-5},$$

**850 times smaller than the log-cosh value**, and buying nothing: the bin-mean residual falls from
2.0966 to 2.0936, 0.14%. So the correlation is *formal only* — the prime side's law is quadratic to the
precision available, with no log-cosh completion. There is also a domain reason it could not have been
otherwise: the expansion of $\log\cosh(t/2)$ converges only for $|t|<\pi$, and the data sit at
$t=\log p\approx20$; three of 3,424,505 handoffs below $10^{9}$ have $t<\pi$. The old theorem's series is
not merely unhelpful at this scale, it is outside its radius of convergence.

This is the good outcome of "revisit the old theorems". The old layer supplied a falsifiable shape; the
new data rejected it; the new law's status — pure $t^{2}$, measured to 0.02%, with no known correction
term — is now sharper than it was.

## 4. What does not carry, and should not be imported

* the **wall** $z=3\pm2\sqrt{2}$ and the peel ODE $\Gamma'=\tfrac{\omega}{2}(1-\Gamma^{2})$: thresholds in
  ratios of ionization energies. The Light Bridge has no ratio of that kind and no √2;
* the **boundary ledger** inequalities (`inverse_le_chord`, `mean_before_inverse_underestimates`) and the
  **round Fisher** metric: real theorems, no counterpart in the closure ladder. Their *lesson* — a linear
  summary of a nonlinear quantity destroys it — is already carried by `linear_mass_law_blind`;
* the **Pauli gram identity** and the two-level spectrum: a different algebra (two orbitals, two levels).

Two things must not be done with this table. The first is to read any row as a derivation: nothing in the
new layer follows from the old one. The second is to read the *form* correspondences as identities of
constants: $\log\cosh(t/2)$'s $1/8$ and the air law's $0.75739$ have no reason to be equal, are not equal,
and the test in §3 is what settles whether a further term carries over — it does not.

## 5. The transferable part, in one line each

1. **A squared-log law is a truncation of something exact** (the old layer's $\log\cosh$). Test the next
   term before trusting the parabola: done here, rejected.
2. **Which laws are forced is itself a theorem** (`SpacingLaw`): a linear-in-$\log$ law is forced by
   multiplicativity; a quadratic one is not, hence measured.
3. **An offset costs a reading** (`ForceRecovery`): the nuclear energy needs one measured table (the mass
   excess), not a better count.
4. **Exclusions are structural** (`PauliMemory` / parity): the classes that cannot occur are proved
   impossible, not found rare.
5. **Counts of an archive are arithmetic, not measurement** (`Archive`): say so, as the old layer does,
   and the new count layer repeats the discipline.
