# Random inputs: do the laws relate, and does the code compute them?

The Lean files prove the identities; that is not in question here. What random testing can add is the
answer to a different question: **is the thing the record computes with the thing that was proved?**
Three programmes, all wired into `scripts/verify-all.sh`:

* `scripts/random_count_relations.py` — the count relations R18–R28 on random inputs: the exact
  ones must not fail, the measured ones must not drift (16,050 draws, 0 failures, no drift across
  four decades) — [`random-counts.md`](random-counts.md);
* `scripts/random_laws.py` — ten property groups on random inputs, checking that the laws hold *in the
  reference implementation* and that the relations close on each other;
* `scripts/random_lean_cross.py` — random cells evaluated in Lean (`#eval` on the proved definitions)
  and compared field by field with that implementation.

## 1. The ten property groups

Run at 20,000 trials each (`python3 scripts/random_laws.py 20000`), all passing:

| # | what is asserted on random input | trials |
|---|---|---|
| 1 | $v+h=L(m)$; the block partition is exact and total; `closed` $\Leftrightarrow$ block $\in\{p,s\}$; group $\in[1,18]$ | 20,000 cells |
| 2 | $Z_1+Z_2=Z$; $h_1+h_2=C_1+C_2-Z$; $Z-Z_1=Z_2$ | 20,000 splits |
| 3 | the pin $h(Z-54)=108-Z$ for random $Z\in[91,108]$; the symmetric switch `closed(Z/2) ⇔ Z≥98` for random even $Z$ | 2×20,000 |
| 4 | the closed-cell windows exactly: 92 → $\{36,37,38\}$, 94 → $\{38\}$, 96 → $\varnothing$ | exhaustive |
| 5 | air $\equiv4\ (6)$; air mod 30 in the five classes; $T=$air$+4\equiv2\ (6)$; class shift $+4$; $V(T)=V(\text{air})+3$ | 400 **real** twin pairs below $10^{11}$ |
| 6 | $\sum T=$ span $+\,2n$ on random twin chains of length 2–7 | 200 chains |
| 7 | $(g+10)\equiv(g+1)\pmod 3$; exactly one of the two grooves divisible by 3 unless $g\equiv1$ | 20,000 gaps |
| 8 | Coulomb $\cap$ magic $=\{2\}$; oscillator $\cap$ magic $=\{2,8,20\}$ | exact |
| 9 | the fissility of a random actinide lies in 30–45 | 20,000 |
| 10 | $\langle\text{air}\rangle=t^2/(2C_2)-2$ at random recorded decades, within six standard errors | 20,000 |

Group 5 is the only one that leaves arithmetic: it draws real twin pairs from below $10^{11}$ and checks
the identities the *primes* are supposed to satisfy, not just the algebra.

## 2. The cross-check that matters

A property test in Python only says that one implementation is self-consistent. The load-bearing test is
whether **Lean's proved definitions** and the record's Python compute the same numbers. `#eval` on
randomly chosen $Z$ gives `(period, cnt, counted, closed)` straight out of `master-theorem.lean`, and the
script compares them:

```
compared 114 random cells: Lean vs the reference implementation
  fields: period, countdown h, counted part v, closed
  all 114 agree
  cells covered: 114 distinct Z, blocks hit: ['d', 'f', 'p', 's']
```

Four of the five blocks are hit by the sample (the fifth, `g`, has no cells below 118), so the agreement
is not confined to one region of the table.

## 3. What it found

One real gap, and it was a usability gap in the formalisation rather than an error: `decide` on
`closed Z` failed, because `closed` is a `def` returning a `Prop` and instance search would not unfold it
for `Decidable`. The master file now carries

```lean
instance closedDecidable (Z : ℕ) : Decidable (closed Z) := by unfold closed; infer_instance
```

without which no random-input check of the closed-cell predicate is possible in Lean at all. That is the
kind of thing a proof cannot notice: the theorem is true whether or not it can be evaluated.

## 4. What random testing cannot do here

It cannot replace any proof, and it should not be read as evidence for the measured laws: group 10 tests
that the *recorded sums* are consistent with the air law to within their own errors — it says nothing
about whether the law is true, which is what the sieve runs in `air-law-offset.md` establish, by
measuring the same quantity at eight decades with a known saddle.

The value is narrower and worth stating plainly: it makes it impossible for the code and the theorem to
drift apart silently. Before this, a change to `period` in one place and not the other would have shown up
only as a wrong number in a document; now it fails `verify-all.sh`.

## 5. Running it

```sh
python3 scripts/random_laws.py 20000     # ten property groups
python3 scripts/random_lean_cross.py 400 # Lean vs the reference implementation
bash scripts/verify-all.sh               # both, plus everything else
```
