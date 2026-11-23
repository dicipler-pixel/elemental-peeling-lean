# Random tests of the count relations: exact ones exact, measured ones stable

`scripts/random_count_relations.py` asks the two different questions the relations R18–R28 need
asking, on random inputs drawn from the real prime chain:

* **exactness** — R18, R19, R20, R21, R22, R23, R28 are arithmetic, so on random draws they must hold
  with **zero failures**. One failure is a bug, not noise.
* **stability** — R24–R27 and the gap law are measurements, so what must be stable is the
  **constant**: estimated on random windows spanning a factor 2 in $x$, it must not drift and must not
  trend with $\log x$.

Both passed. Nothing below is a proof of anything: the identities are already proved in
[`count-formulas.lean`](count-formulas.lean) — these tests catch the other failure mode, the one a
proof cannot, where the script and the theorem have drifted apart.

## 1. The run

`python3 scripts/random_count_relations.py 2000 1e9` — 16,050 checks, 0 failed, 13 s:

| group | what it draws | checks | failed |
|---|---|---|---|
| R18 $P=B+K+2$ | 2000 random bounds $x\le10^9$ | 2000 | **0** |
| R19 twin $>3$ is $5\ (6)$; $N\le K+1$ | 2000 random twin starts + 2000 random bounds | 4000 | **0** |
| R20 twin $>5$ is $11,17,29\ (30)$ | 2000 random twin starts | 2000 | **0** |
| R21 air $\equiv4\ (6)$, total $\equiv2\ (6)$ | 2000 random handoffs | 2000 | **0** |
| R22 quadruplet $\Rightarrow p\equiv11\ (30)$ | 2000 random air-$4$ merges | 2000 | **0** |
| R23 $\sum\text{air}=\text{span}-2\hat N$ | 2000 random windows, 1–500 handoffs wide | 2000 | **0** |
| R28 segments $=\hat N-D+1$ | 2000 random windows, 1–200 handoffs wide | 2000 | **0** |
| Lean vs the sieve | 49 random bounds $\le200$, five counts each | 49 | **0** |
| stability | 400 windows, 289 usable | 1 | **0** |

At $10^8$ the same run is 16,052 checks with 0 failures, and three further seeds (1000 trials each,
8001 checks apiece) are also 0 failures — so the result is not a seed.

**Two exceptions exist, and they are exactly the hypotheses the theorems already declare.** The random
test found them and nothing else:

* the handoff $(3,5)\to(5,7)$ has air $0$, the one handoff not $\equiv4\pmod6$ — the same $p>3$ that
  `air_mod_six` requires;
* the quadruplet $(5,7,11,13)$ starts at $p=5\not\equiv11\pmod{30}$ — the same $p>5$ that
  `quadruplet_start_mod_30` requires.

That is the useful outcome of a random test on a proved statement: the only failures it can find are
at the boundary the statement names.

## 2. Stability: 289 random windows, factor 2 in $x$, up to $10^9$

Each window gives its own estimate of the constant. `drift` is the correlation of that estimate with
$\log x$ — zero means the constant does not move as the numbers grow.

| law | estimate (mean) | s.d. | min | max | drift vs $\log x$ | within 25% |
|---|---|---|---|---|---|---|
| R25 $N/(2C_2\mathrm{Li}_2)$ | **1.0036** | 0.045 | 0.825 | 1.263 | $-0.12$ | **99.7%** |
| R27 $D/\hat N\div(2C_2/\log x)$ | **1.0168** | 0.152 | 0.535 | 1.880 | $-0.04$ | 90.3% |
| R26 $D/((2C_2)^2\mathrm{Li}_3)$ | **1.0181** | 0.163 | 0.474 | 1.852 | $-0.05$ | 88.2% |
| gap law $\langle\text{gap}\rangle/(t^2/2C_2)$ | **0.9960** | 0.045 | 0.770 | 1.202 | $+0.12$ | **100.0%** |

Split into four log-quartiles, the same four numbers, to show there is no trend hiding in the mean:

| range of $x$ | $N$ | $D/\hat N$ | $D$ density | gap |
|---|---|---|---|---|
| $1.8\cdot10^5$–$1.4\cdot10^6$ | 1.009 | 1.042 | 1.044 | 0.990 |
| $1.5\cdot10^6$–$1.0\cdot10^7$ | 1.007 | 0.997 | 1.003 | 0.992 |
| $1.0\cdot10^7$–$7.0\cdot10^7$ | 0.999 | 1.018 | 1.016 | 1.002 |
| $7.2\cdot10^7$–$4.9\cdot10^8$ | 0.999 | 1.010 | 1.009 | 1.001 |

So: the twin constant is stable to $4\%$ per window and unbiased at $0.4\%$; the gap law to $4\%$ and
unbiased at $0.4\%$; the merge laws to $15$–$16\%$ per window and biased $+1.7$–$+1.8\%$, which is the
same $1$–$2\%$ the note on [`count-formulas.md`](count-formulas.md) §4 quotes as the accuracy of
$D$'s formula. No law drifts: every $|\text{drift}|\le0.12$, i.e.\ none of the four constants moves
across four decades.

## 3. What the random test does not do

* It does not re-prove the identities — it samples them. Over 16,000 draws with no failure, a hidden
  counterexample below $10^9$ is not excluded; the Lean proofs are what exclude it.
* It does not test the laws outside the range $10^4$–$10^9$. The record's air law is measured to
  $10^{12}$ elsewhere ([`air-law-offset.md`](air-law-offset.md)); this script's job is the relations,
  not a new measurement of the constants at large height.
* The Lean cross-check compares `baseCount`, `ladderCount`, `twinCount`, `primesUpTo` and `handoffs`
  against the sieve on 49 random bounds $\le200$ — the bound is small because `#eval` on the kernel's
  `Nat.Prime` is what is being run, not because the definition is restricted.
